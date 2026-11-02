use std::cmp::Ordering;

use citationberg::taxonomy::Variable;
use citationberg::{
    InheritableNameOptions, LocaleCode, LongShortForm, Sort, SortDirection, SortKey,
};
use icu_collator::options::{CollatorOptions, Strength};
use icu_collator::{Collator, CollatorPreferences};
use icu_locale::Locale as IcuLocale;

use crate::csl::BufWriteFormat;
use crate::csl::rendering::RenderCsl;

use super::taxonomy::EntryLike;
use super::{CitationItem, InstanceContext, StyleContext};

/// Remove punctuation from a sort key while preserving spaces, mirroring
/// citeproc-js's `ignorePunctuation: true`. Leading quotation marks,
/// brackets and apostrophes are dropped, and internal apostrophes are
/// removed (they are punctuation in `localeCompare`).
pub(crate) fn normalize_sort_key(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_alphanumeric() || c.is_whitespace() {
            out.push(c);
        }
    }
    out
}

/// The sort component of one person, honoring the style's
/// `demote-non-dropping-particle` setting.
pub(crate) fn person_sort_key(person: &crate::types::Person, demote: bool) -> String {
    let mut key = String::new();
    if demote {
        key.push_str(&normalize_name_sort_key(person.name_without_particle()));
        key.push(' ');
        if let Some(given) = &person.given_name {
            key.push_str(&normalize_name_sort_key(given));
        }
        if let Some(particle) = person.name_particle() {
            key.push(' ');
            key.push_str(&normalize_name_sort_key(particle));
        }
    } else {
        if let Some(particle) = &person.non_dropping_particle {
            key.push_str(&normalize_name_sort_key(particle));
            key.push(' ');
        }
        key.push_str(&normalize_name_sort_key(&person.name));
        key.push(' ');
        if let Some(given) = &person.given_name {
            key.push_str(&normalize_name_sort_key(given));
        }
    }
    key
}

/// Name sort keys follow citeproc-js's structured name keys: an apostrophe
/// splits the family name into separately collated components (`d'Wander`
/// -> `d`, `Wander`), and joining words are not part of the key.
pub(crate) fn normalize_name_sort_key(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if c == '\'' || c == '\u{2019}' {
            out.push(' ');
        } else if c.is_alphanumeric() || c.is_whitespace() {
            out.push(c);
        }
    }
    out.split_whitespace()
        .filter(|word| !word.eq_ignore_ascii_case("and") && *word != "&")
        .collect::<Vec<_>>()
        .join(" ")
}

trait CollationOrd: Ord {
    fn collation_cmp(&self, other: &Self, locale: LocaleCode) -> Ordering;
}

impl CollationOrd for str {
    fn collation_cmp(&self, other: &Self, locale: LocaleCode) -> Ordering {
        if let Ok(locale) = locale.0.parse::<IcuLocale>() {
            // citeproc-js compares sort keys with `localeCompare` configured
            // as `sensitivity: "base"`, `ignorePunctuation: true`, and
            // `numeric: true`. Mirror all three: base letters only (case and
            // accents are ignored), punctuation removed before comparison
            // (spaces stay significant), and digit runs compared by value.
            let mut options = CollatorOptions::default();
            options.strength = Some(Strength::Primary);
            let preferences: CollatorPreferences = locale.into();
            let collator = Collator::try_new(preferences, options).unwrap();
            let a = normalize_sort_key(self);
            let b = normalize_sort_key(other);
            collator.compare(&a, &b)
        } else {
            self.cmp(other)
        }
    }
}

impl<T: CollationOrd> CollationOrd for Option<T> {
    fn collation_cmp(&self, other: &Self, locale: LocaleCode) -> Ordering {
        match (self, other) {
            (Some(a), Some(b)) => a.collation_cmp(b, locale),
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}

impl CollationOrd for String {
    fn collation_cmp(&self, other: &Self, locale: LocaleCode) -> Ordering {
        CollationOrd::collation_cmp(self as &str, other, locale)
    }
}

impl StyleContext<'_> {
    /// Retrieve the ordering of two entries according to the given sort key.
    fn cmp_entries<T: EntryLike>(
        &self,
        a: &CitationItem<T>,
        a_idx: usize,
        b: &CitationItem<T>,
        b_idx: usize,
        key: &SortKey,
        term_locale: Option<&LocaleCode>,
        bibliography: bool,
    ) -> Ordering {
        let (ordering, empty_value) = match key {
            SortKey::Variable { variable: Variable::Standard(s), .. } => {
                let a = InstanceContext::variable_sort_instance(a, a_idx)
                    .resolve_standard_variable(LongShortForm::default(), *s)
                    .map(|s| s.to_string().to_lowercase());
                let b = InstanceContext::variable_sort_instance(b, b_idx)
                    .resolve_standard_variable(LongShortForm::default(), *s)
                    .map(|s| s.to_string().to_lowercase());

                (a.collation_cmp(&b, self.locale()), a.is_none() || b.is_none())
            }
            SortKey::Variable { variable: Variable::Date(d), .. } => {
                let a = a.entry.resolve_date_range(*d);
                let b = b.entry.resolve_date_range(*d);

                match (a, b) {
                    // citeproc-js's date sort key carries the end parts after
                    // the start parts, so equal starts are ordered by their
                    // ends (`sort_DateVariableRange`).
                    (Some(a), Some(b)) => (a.csl_cmp(&b), false),
                    (Some(_), None) => (Ordering::Greater, true),
                    (None, Some(_)) => (Ordering::Less, true),
                    (None, None) => (Ordering::Equal, true),
                }
            }
            SortKey::Variable { variable: Variable::Name(n), .. } => {
                // citeproc-js builds a structured key for name variables:
                // each person contributes its family-name components followed
                // by the given name, with apostrophes splitting family
                // components (`d'Wander` -> `d`, `Wander`) and joining words
                // left out. Comparing the same shape keeps particle-less CJK
                // and apostrophe names in citeproc order.
                let demote = self.csl.settings.demote_non_dropping_particle
                    != citationberg::DemoteNonDroppingParticle::Never;
                let key = |entry: &CitationItem<T>| {
                    let people = entry.entry.resolve_name_variable(*n);
                    let mut key = String::new();
                    for (idx, person) in people.iter().enumerate() {
                        if idx > 0 {
                            key.push(' ');
                        }
                        key.push_str(&person_sort_key(person, demote));
                    }
                    key
                };
                let a_key = key(a);
                let b_key = key(b);
                (a_key.collation_cmp(&b_key, self.locale()), false)
            }
            SortKey::Variable { variable: Variable::Number(n), .. } => {
                let a = InstanceContext::variable_sort_instance(a, a_idx)
                    .resolve_number_variable(*n);
                let b = InstanceContext::variable_sort_instance(b, b_idx)
                    .resolve_number_variable(*n);

                match (a, b) {
                    (Some(a), Some(b)) => (a.csl_cmp(&b), false),
                    (Some(_), None) => (Ordering::Greater, true),
                    (None, Some(_)) => (Ordering::Less, true),
                    (None, None) => (Ordering::Equal, true),
                }
            }
            SortKey::Variable { variable: Variable::Page(pv), .. } => {
                let a = InstanceContext::variable_sort_instance(a, a_idx)
                    .resolve_page_variable(*pv);
                let b = InstanceContext::variable_sort_instance(b, b_idx)
                    .resolve_page_variable(*pv);

                match (a, b) {
                    (Some(a), Some(b)) => (a.csl_cmp(&b), false),
                    (Some(_), None) => (Ordering::Greater, true),
                    (None, Some(_)) => (Ordering::Less, true),
                    (None, None) => (Ordering::Equal, true),
                }
            }
            SortKey::MacroName {
                name,
                names_min,
                names_use_first,
                names_use_last,
                ..
            } => {
                let render = |entry: &CitationItem<T>, idx: usize| {
                    let mut ctx = self.macro_sorting_ctx(
                        entry,
                        idx,
                        entry.locale.as_ref(),
                        term_locale,
                        bibliography,
                    );
                    ctx.writing.push_name_options(&InheritableNameOptions {
                        et_al_min: *names_min,
                        et_al_subsequent_min: *names_min,
                        et_al_use_first: *names_use_first,
                        et_al_subsequent_use_first: *names_use_first,
                        et_al_use_last: *names_use_last,
                        ..Default::default()
                    });

                    self.get_macro(name).map(|m| {
                        for child in &m.children {
                            child.render(&mut ctx)
                        }
                        let saw_names = ctx.saw_names;
                        let rendered =
                            ctx.flush().0.into_iter().fold(String::new(), |mut s, f| {
                                f.write_buf(&mut s, BufWriteFormat::Plain).unwrap();
                                s
                            });
                        let out = if saw_names {
                            normalize_name_sort_key(&rendered)
                        } else {
                            normalize_sort_key(&rendered)
                        };
                        out
                    })
                };

                let a_rendered = render(a, a_idx);
                let b_rendered = render(b, b_idx);
                (a_rendered.collation_cmp(&b_rendered, self.locale()), false)
            }
        };

        // Per CSL 1.0.2 spec (https://docs.citationstyles.org/en/v1.0.2/specification.html):
        // Entries with empty values are always displayed at the end, even with reversed order.
        // So we always reverse the order if either entry is empty.
        if empty_value || key.sort_direction() == SortDirection::Descending {
            ordering.reverse()
        } else {
            ordering
        }
    }

    /// Compare two already-normalized sort keys with the style's locale
    /// collation. Cite grouping uses the same comparison as sorting.
    pub(crate) fn compare_sort_strings(&self, a: &str, b: &str) -> Ordering {
        a.collation_cmp(b, self.locale())
    }

    /// The string citeproc-js uses as the first key of a cite group: the
    /// value of the first sort key (an internal name key when the key is a
    /// names macro), normalized for comparison.
    pub(crate) fn group_sort_key<T: EntryLike>(
        &self,
        item: &CitationItem<T>,
        idx: usize,
        key: &SortKey,
        term_locale: Option<&LocaleCode>,
    ) -> (String, bool) {
        match key {
            SortKey::Variable { variable, .. } => match variable {
                Variable::Standard(s) => (
                    InstanceContext::variable_sort_instance(item, idx)
                        .resolve_standard_variable(LongShortForm::default(), *s)
                        .map(|s| normalize_sort_key(&s.to_string()))
                        .unwrap_or_default(),
                    false,
                ),
                Variable::Date(d) => (
                    item.entry
                        .resolve_date_range(*d)
                        .map(|d| {
                            // The group key mirrors the date sort key: start
                            // parts followed by the end parts.
                            let mut key = format!(
                                "{:09}{:02}{:02}",
                                d.start.year + 100_000,
                                d.start.month.unwrap_or(0),
                                d.start.day.unwrap_or(0)
                            );
                            if let Some(end) = d.end {
                                key.push_str(&format!(
                                    "{:09}{:02}{:02}",
                                    end.year + 100_000,
                                    end.month.unwrap_or(0),
                                    end.day.unwrap_or(0)
                                ));
                            }
                            key
                        })
                        .unwrap_or_default(),
                    false,
                ),
                Variable::Name(n) => {
                    let people = item.entry.resolve_name_variable(*n);
                    let demote = self.csl.settings.demote_non_dropping_particle
                        != citationberg::DemoteNonDroppingParticle::Never;
                    let mut key = String::new();
                    for (i, person) in people.iter().enumerate() {
                        if i > 0 {
                            key.push(' ');
                        }
                        key.push_str(&person_sort_key(person, demote));
                    }
                    (key, true)
                }
                Variable::Number(n) => (
                    InstanceContext::variable_sort_instance(item, idx)
                        .resolve_number_variable(*n)
                        .map(|n| match n {
                            crate::csl::taxonomy::NumberVariableResult::Regular(n) => {
                                n.to_string()
                            }
                            crate::csl::taxonomy::NumberVariableResult::Transparent(
                                i,
                            ) => i.to_string(),
                        })
                        .unwrap_or_default(),
                    false,
                ),
                Variable::Page(p) => (
                    InstanceContext::variable_sort_instance(item, idx)
                        .resolve_page_variable(*p)
                        .map(|p| p.to_string())
                        .unwrap_or_default(),
                    false,
                ),
            },
            SortKey::MacroName {
                name,
                names_min,
                names_use_first,
                names_use_last,
                ..
            } => {
                let mut ctx = self.macro_sorting_ctx(
                    item,
                    idx,
                    item.locale.as_ref(),
                    term_locale,
                    false,
                );
                ctx.writing.push_name_options(&InheritableNameOptions {
                    et_al_min: *names_min,
                    et_al_subsequent_min: *names_min,
                    et_al_use_first: *names_use_first,
                    et_al_subsequent_use_first: *names_use_first,
                    et_al_use_last: *names_use_last,
                    ..Default::default()
                });
                self.get_macro(name)
                    .map(|m| {
                        for child in &m.children {
                            child.render(&mut ctx);
                        }
                        let saw_names = ctx.saw_names;
                        let rendered =
                            ctx.flush().0.into_iter().fold(String::new(), |mut s, f| {
                                f.write_buf(&mut s, BufWriteFormat::Plain).unwrap();
                                s
                            });
                        if saw_names {
                            (normalize_name_sort_key(&rendered), true)
                        } else {
                            (normalize_sort_key(&rendered), false)
                        }
                    })
                    .unwrap_or_default()
            }
        }
    }

    /// Sorts the given citation items by the style's sort keys.
    pub fn sort<T: EntryLike>(
        &self,
        cites: &mut [CitationItem<T>],
        sort: Option<&Sort>,
        term_locale: Option<&LocaleCode>,
        bibliography: bool,
        citation_number: impl Fn(&T) -> usize,
    ) {
        if let Some(sort) = sort {
            cites.sort_by(|a, b| {
                let mut ordering = Ordering::Equal;
                for key in &sort.keys {
                    ordering = self.cmp_entries(
                        a,
                        citation_number(a.entry),
                        b,
                        citation_number(b.entry),
                        key,
                        term_locale,
                        bibliography,
                    );
                    if ordering != Ordering::Equal {
                        break;
                    }
                }
                ordering
            });
        }
    }
}

/// Public-in-crate wrapper used by citation grouping.
pub(crate) fn normalize_name_sort_key_public(s: &str) -> String {
    normalize_name_sort_key(s)
}
