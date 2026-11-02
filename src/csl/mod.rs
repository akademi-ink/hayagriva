use std::any::Any;
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::hash_map::Entry as HmEntry;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Write};
use std::hash::Hash;
use std::num::{NonZeroI16, NonZeroUsize};
use std::sync::Arc;
use std::{mem, vec};

use citationberg::taxonomy::{
    DateVariable, Locator, NameVariable, NumberOrPageVariable, NumberVariable, OtherTerm,
    PageVariable, StandardVariable, Term, Variable,
};
use citationberg::{
    Affixes, BaseLanguage, Choose, Citation, CitationFormat, Collapse, CslMacro,
    DisambiguationRule, Display, GrammarGender, Group, IndependentStyle,
    InheritableNameOptions, Layout, LayoutRenderingElement, Locale, LocaleCode, Names,
    SecondFieldAlign, StyleCategory, StyleClass, SubsequentAuthorSubstituteRule,
    TermForm, Text, ToAffixes, ToFormatting, taxonomy as csl_taxonomy,
};
use citationberg::{DateForm, LongShortForm, OrdinalLookup, TextCase};
use indexmap::IndexSet;

use crate::csl::elem::{
    NonEmptyStack, coalesce_text_runs, simplify_children, trim_trailing_whitespace,
};
use crate::csl::rendering::names::{DisambiguatedNameForm, NameDisambiguationProperties};
use crate::csl::rendering::{
    RenderCsl, format_page_string, page_string_is_plural, split_embedded_locator_label,
};
use crate::csl::taxonomy::NumberOrPageVariableResult;
use crate::lang::{Case, CaseFolder};
use crate::types::{ChunkKind, ChunkedString, Date, MaybeTyped, Person};

use self::elem::last_text_mut_child;
pub use self::elem::{
    BufWriteFormat, Elem, ElemChild, ElemChildren, ElemMeta, Formatted, Formatting,
};
use self::quotes::{QuoteMarks, SmartQuoter};
use self::taxonomy::{EntryLike, NumberVariableResult, PageVariableResult};

#[cfg(feature = "archive")]
pub mod archive;
mod citation_label;
mod elem;
mod quotes;
mod rendering;
mod sort;
mod taxonomy;

/// This struct formats a set of citations according to a style.
#[derive(Debug)]
pub struct BibliographyDriver<'a, T: EntryLike> {
    /// The citations we have seen so far.
    citations: Vec<CitationRequest<'a, T>>,
    /// Offset to apply to the citation number (for numeric styles).
    citation_number_offset: usize,
}

impl<T: EntryLike> Default for BibliographyDriver<'_, T> {
    fn default() -> Self {
        Self { citations: Vec::new(), citation_number_offset: 0 }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct SpeculativeItemRender<'a, T: EntryLike> {
    rendered: ElemChildren,
    /// The item rendered for ambiguity detection. citeproc-js always scans
    /// the "subsequent" cite form (`position="subsequent"`, `near-note` true,
    /// no locator or affixes), so two items whose first forms differ can
    /// still clash for disambiguation (`disambiguate_BasedOnSubsequentFormWithBackref2`,
    /// `bugreports_EnvAndUrb`).
    ambiguity_rendered: ElemChildren,
    entry: &'a T,
    cite_props: CiteProperties<'a>,
    checked_disambiguate: bool,
    first_name: Option<NameDisambiguationProperties>,
    delim_override: Option<&'a str>,
    group_idx: Option<usize>,
    locator: Option<SpecificLocator<'a>>,
    hidden: bool,
    locale: Option<LocaleCode>,
    purpose: Option<CitePurpose>,
    prefix: Option<String>,
    suffix: Option<String>,
    collapse_verdict: Option<CollapseVerdict>,
    style_uses_year_suffix_var: bool,
}

#[derive(Debug, PartialEq)]
struct SpeculativeCiteRender<'a, 'b, T: EntryLike> {
    items: Vec<SpeculativeItemRender<'a, T>>,
    request: &'b CitationRequest<'a, T>,
}

/// Returns the inter-item delimiter to place before an item, mirroring
/// citeproc-js's suppression rules for item affixes (cf. the test case
/// `magic_SuppressLayoutDelimiterIfPrefixComma`).
///
/// If the preceding item's suffix ends in `;`, `.` or `,`, only the part of
/// the delimiter from its first space onwards is kept. If the current item's
/// prefix starts with one of those characters, the delimiter is dropped
/// entirely. Returns `None` if no delimiter should be printed.
fn item_delimiter<'a, T: EntryLike>(
    prev: &SpeculativeItemRender<'a, T>,
    item: &SpeculativeItemRender<'a, T>,
    delimiter: &'a str,
) -> Option<&'a str> {
    const TERMINAL: [char; 3] = [';', '.', ','];

    let prev_ends_with_terminal = prev
        .suffix
        .as_deref()
        .and_then(|s| s.chars().next_back())
        .is_some_and(|c| TERMINAL.contains(&c));
    let item_starts_with_terminal = prev.suffix.is_none()
        && item
            .prefix
            .as_deref()
            .and_then(|s| s.chars().next())
            .is_some_and(|c| TERMINAL.contains(&c));

    if prev_ends_with_terminal {
        if item_starts_with_terminal {
            None
        } else {
            // Keep the part of the delimiter starting at its first space or
            // drop it if it contains none.
            Some(delimiter.find(' ').map_or("", |i| &delimiter[i..]))
        }
    } else if item_starts_with_terminal {
        None
    } else {
        Some(delimiter)
    }
}

/// Whether a citation item prefix reads like a complete sentence, i.e. it
/// ends in terminal punctuation after at least one space.
///
/// Mirrors citeproc-js's `checkIgnorePredecessor`: only such prefixes make a
/// following term start a new sentence (and thus be capitalized).
fn prefix_starts_sentence(prefix: &str) -> bool {
    let trimmed = prefix.trim_end_matches(|c: char| {
        c.is_whitespace()
            || matches!(c, '"' | '\'' | '\u{201d}' | '\u{2019}' | '\u{00bb}' | '\u{202f}')
    });
    let ends_in_terminal_punctuation =
        matches!(trimmed.chars().next_back(), Some(':' | '.' | ';' | '!' | '?'));
    ends_in_terminal_punctuation && prefix.trim().contains(' ')
}

/// Capitalize the first character of a term.
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

/// Whether a citation or element suffix should be printed.
///
/// Mirrors citeproc-js: a suffix is collapsed only when it duplicates
/// terminal punctuation already present ("." after "."), never closing
/// delimiters — content ending in `)` plus a `)` suffix renders `))`.
fn should_print_suffix(last_text: Option<&str>, suffix: &str) -> bool {
    let terminal = |s: &str| {
        !s.is_empty() && s.chars().all(|c| matches!(c, '.' | ',' | ';' | ':' | '!' | '?'))
    };
    last_text.is_none_or(|t| !(terminal(suffix) && t.ends_with(suffix)))
}

/// Move the leading punctuation of `text` into a trailing closing quote in
/// `children`, if there is one. `text` keeps the punctuation if it could not
/// be moved inside a quote.
fn pull_leading_punctuation(
    children: &mut [ElemChild],
    text: &mut String,
    marks: &QuoteMarks,
) {
    let Some(punct) = text
        .chars()
        .next()
        .filter(|c| matches!(c, '.' | ',' | ';' | '!' | '?'))
    else {
        return;
    };

    if let Some(last) = last_text_mut_child(children)
        && quotes::move_punctuation_inside(&mut last.text, punct, marks)
    {
        text.remove(0);
    }
}

impl<'a, T: EntryLike> BibliographyDriver<'a, T> {
    /// Create a new bibliography driver.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a citation number offset to the driver.
    ///
    /// This is used when determining the number of numeric styles. When a
    /// citation would usually be numbered `[1]` and this is set to `2`, it
    /// would be numbered as `[3]`.
    ///
    /// This is primarily useful when managing multiple bibliographies.
    pub fn with_citation_number_offset(mut self, offset: usize) -> Self {
        self.citation_number_offset = offset;
        self
    }

    /// Create a new citation with the given items.
    pub fn citation(&mut self, mut req: CitationRequest<'a, T>) {
        for (i, item) in req.items.iter_mut().enumerate() {
            item.initial_idx = i;
        }
        self.citations.push(req);
    }
}

/// Implementations for finishing the bibliography.
impl<T: EntryLike + Hash + PartialEq + Eq + Debug> BibliographyDriver<'_, T> {
    /// Render the bibliography.
    pub fn finish(mut self, request: BibliographyRequest<'_>) -> Rendered {
        // 1.  Assign citation numbers by bibliography ordering or by citation
        //     order and render them a first time without their locators.
        let bib_style = request.style();

        // Only remember each entry once, even if it is cited multiple times.
        let mut entry_set = IndexSet::new();
        for req in self.citations.iter() {
            for item in req.items.iter() {
                entry_set.insert(item.entry);
            }
        }

        // Names for given-name disambiguation rules other than `by-cite` are
        // counted document-wide (citeproc-js's name register).
        let name_variables = style_name_variables(bib_style.csl);
        let mut name_registry = NameRegistry::default();
        if !name_variables.is_empty() {
            // `primary-name*` rules only ever compare the first name of each
            // nameset (citeproc-js passes the person index to `addname` and
            // skips it for the rest).
            let primary_only = matches!(
                bib_style.csl.citation.givenname_disambiguation_rule,
                DisambiguationRule::PrimaryName
                    | DisambiguationRule::PrimaryNameWithInitials
            ) && bib_style.csl.citation.disambiguate_add_givenname;
            for entry in entry_set.iter() {
                for variable in &name_variables {
                    for (idx, person) in
                        entry.resolve_name_variable(*variable).into_iter().enumerate()
                    {
                        if primary_only && idx > 0 {
                            continue;
                        }
                        name_registry.register(person.as_ref());
                    }
                }
            }
        }

        let mut entries: Vec<_> =
            entry_set.into_iter().map(CitationItem::with_entry).collect();
        bib_style.sort(
            &mut entries,
            bib_style.csl.bibliography.as_ref().and_then(|b| b.sort.as_ref()),
            request.locale.as_ref(),
            |_| 0,
        );
        let citation_number = |item: &T| {
            self.citation_number_offset
                + entries.iter().position(|e| e.entry == item).expect("entry not found")
        };

        // citeproc-js assigns citation numbers lazily: when a citation is
        // appended, the entries known so far are numbered by the bibliography
        // sort restricted to them. Later citations can therefore introduce a
        // number that precedes the numbers of earlier citations (e.g. an
        // alphabetically earlier author first cited last), and the numbers
        // shown in a citation reflect that state at append time. The engine
        // renders all citations in one pass, so we track the entries cited up
        // to each citation and number only those.
        let bibliography_sorts = bib_style
            .csl
            .bibliography
            .as_ref()
            .and_then(|b| b.sort.as_ref())
            .is_some();
        let mut cited: HashSet<*const T> = HashSet::new();

        let mut seen: HashSet<*const T> = HashSet::new();
        let mut res: Vec<SpeculativeCiteRender<T>> = Vec::new();
        let mut last_cite: Option<&CitationItem<T>> = None;

        for citation in &mut self.citations {
            let mut style = citation.style();
            style.name_registry = Some(&name_registry);

            let numbering: HashMap<*const T, usize> = if bibliography_sorts {
                cited.extend(citation.items.iter().map(|item| item.entry as *const T));
                let mut map = HashMap::with_capacity(cited.len());
                let mut number = self.citation_number_offset;
                for entry in entries.iter() {
                    if cited.contains(&(entry.entry as *const T)) {
                        map.insert(entry.entry as *const T, number);
                        number += 1;
                    }
                }
                map
            } else {
                HashMap::new()
            };
            let number_for = |item: &T| {
                if bibliography_sorts {
                    *numbering.get(&(item as *const T)).expect("entry not numbered")
                } else {
                    citation_number(item)
                }
            };

            style.sort(
                &mut citation.items,
                style.csl.citation.sort.as_ref(),
                citation.locale.as_ref(),
                number_for,
            );

            let items = &citation.items;
            let mut renders: Vec<SpeculativeItemRender<'_, T>> = Vec::new();

            for item in items.iter() {
                let entry = &item.entry;

                let is_near_note = citation.note_number.is_some_and(|_| {
                    res.iter()
                        .rev()
                        .take(style.csl.citation.near_note_distance as usize)
                        .any(|cite| {
                            cite.request.note_number.is_some()
                                && cite.items.iter().any(|item| &item.entry == entry)
                        })
                });

                let first_note_number = citation.note_number.map(|n| {
                    res.iter()
                        .find_map(|cite| {
                            cite.request.note_number.filter(|_| {
                                cite.items.iter().any(|item| &item.entry == entry)
                            })
                        })
                        .unwrap_or(n)
                });

                let mut cite_props = CiteProperties {
                    certain: CertainCiteProperties {
                        note_number: citation.note_number,
                        first_note_number,
                        is_near_note,
                        position: item.position,
                        near_note: item.near_note,
                        is_first: seen.insert(*entry),
                        initial_idx: item.initial_idx,
                    },
                    speculative: SpeculativeCiteProperties::speculate(
                        None,
                        number_for(entry),
                        IbidState::with_last(item, last_cite),
                    ),
                };

                let ctx = style.do_citation(
                    *entry,
                    cite_props.clone(),
                    item.locale.as_ref(),
                    citation.locale.as_ref(),
                    item.purpose,
                    None,
                    item.prefix.as_deref(),
                );

                // Copy the identifier usage from the context. Assume it does
                // not change throughout disambiguation.
                cite_props.speculative.identifier_usage =
                    ctx.instance.identifier_usage.take();

                let first_name = ctx.writing.first_name.clone();
                let checked_disambiguate = ctx.writing.checked_disambiguate;
                let rendered = ctx.flush();
                let ambiguity_rendered = ambiguity_render(
                    &style,
                    *entry,
                    &cite_props,
                    item.locale.as_ref(),
                    item.purpose,
                    citation,
                );
                renders.push(SpeculativeItemRender {
                    entry,
                    cite_props,
                    checked_disambiguate,
                    first_name,
                    delim_override: None,
                    group_idx: None,
                    locator: item.locator.clone(),
                    rendered,
                    ambiguity_rendered,
                    hidden: item.hidden,
                    locale: item.locale.clone(),
                    purpose: item.purpose,
                    prefix: item.prefix.clone(),
                    suffix: item.suffix.clone(),
                    collapse_verdict: None,
                    style_uses_year_suffix_var: uses_year_suffix_var(&style),
                });

                last_cite = Some(item);
            }

            let mut cite = SpeculativeCiteRender { items: renders, request: citation };
            apply_grouped_sort(&style, &mut cite, citation.locale.as_ref());
            res.push(cite);
        }

        // 2.  Disambiguate the citations.
        //
        // If we have set the disambiguation state for an item, we need to set
        // the same state for all entries referencing that item.
        //
        // citeproc-js assigns year suffix letters in bibliography order
        // ("the assignment of year-suffixes follows the order of the
        // bibliographies entries"), so capture that rank once.
        let bib_rank: HashMap<*const T, usize> = entries
            .iter()
            .enumerate()
            .map(|(idx, item)| (item.entry as *const T, idx))
            .collect();
        let disambiguate_levels = style_disambiguate_levels(bib_style.csl);
        let mut choose_resolved: HashSet<*const T> = HashSet::new();
        for _ in 0..(4 + disambiguate_levels as usize) {
            let ambiguous = find_ambiguous_sets(&res, &choose_resolved);
            if ambiguous.is_empty() {
                break;
            }

            let mut rerender: HashMap<*const T, DisambiguateState> = HashMap::new();
            let mut suffixes: HashMap<*const T, u8> = HashMap::new();
            let mark = |map: &mut HashMap<*const T, DisambiguateState>,
                        entry: &T,
                        state: DisambiguateState| {
                map.entry(entry)
                    .and_modify(|e| *e = e.clone().max(state.clone()))
                    .or_insert(state);
            };

            for group in ambiguous.iter() {
                let len_rerender = rerender.len() + suffixes.len();
                // 2a. Name Disambiguation loop
                disambiguate_names(&res, group, |entry, state| {
                    mark(&mut rerender, entry, state)
                });

                // Do not try other methods for this group if the previous method succeeded.
                if rerender.len() + suffixes.len() > len_rerender {
                    continue;
                }

                // 2b. Disambiguate by allowing `cs:choose` disambiguation.
                disambiguate_with_choose(
                    &res,
                    group,
                    |entry, state| mark(&mut rerender, entry, state),
                    &mut choose_resolved,
                );

                if rerender.len() + suffixes.len() > len_rerender {
                    continue;
                }

                // 2c. Disambiguate by year-suffix.
                disambiguate_year_suffix(&res, group, &bib_rank, |entry, suffix| {
                    suffixes.insert(entry as *const T, suffix);
                });
            }

            if rerender.is_empty() && suffixes.is_empty() {
                break;
            }

            for cite in res.iter_mut() {
                let mut style_ctx = cite.request.style();
                style_ctx.name_registry = Some(&name_registry);
                for item in cite.items.iter_mut() {
                    let mut rerender_item = false;
                    if let Some(state) = rerender.get(&(item.entry as _)) {
                        item.cite_props.speculative.disambiguation = state.clone();
                        rerender_item = true;
                    }
                    if let Some(suffix) = suffixes.get(&(item.entry as _)) {
                        item.cite_props.speculative.year_suffix = Some(*suffix);
                        rerender_item = true;
                    }
                    if rerender_item {
                        item.rendered = do_rerender(&style_ctx, item, cite.request);
                        item.ambiguity_rendered = ambiguity_render(
                            &style_ctx,
                            item.entry,
                            &item.cite_props,
                            item.locale.as_ref(),
                            item.purpose,
                            cite.request,
                        );
                    }
                }
            }
        }

        // 3. Group adjacent citations.
        //
        // A cite group is a run of adjacent items that render the same names
        // element: like citeproc-js, each item is compared with its immediate
        // predecessor only. Non-adjacent items with the same names start a new
        // group (and receive a fresh `group_idx`), and item order is never
        // changed.
        for cite in res.iter_mut() {
            let Some(delim) =
                cite.request.style.citation.cite_group_delimiter.as_deref().or_else(
                    || {
                        cite.request
                            .style
                            .citation
                            .layout
                            .delimiter
                            .as_deref()
                            .filter(|_| cite.request.style.citation.collapse.is_some())
                    },
                )
            else {
                continue;
            };

            let mut group_idx = 0;
            let mut prev_name_elem: Option<String> = None;
            let fallback_author_key = matches!(
                cite.request.style.citation.collapse,
                Some(Collapse::YearSuffix | Collapse::YearSuffixRanged)
            );

            for item in cite.items.iter_mut() {
                let name_elem = item.rendered.find_names().map(names_key).or_else(|| {
                    fallback_author_key.then(|| entry_author_key(item.entry))
                });

                match name_elem {
                    Some(name_elem) => {
                        if prev_name_elem.as_deref() == Some(name_elem.as_str()) {
                            // Only items that continue the current cite group
                            // are joined to the preceding item with the
                            // cite-group delimiter. The first item of each
                            // group keeps the citation layout delimiter.
                            item.delim_override = Some(delim);
                        } else {
                            group_idx += 1;
                        }
                        item.group_idx = Some(group_idx);
                        prev_name_elem = Some(name_elem);
                    }
                    // An item without a names element cannot be part of a
                    // group and also breaks adjacency for the next item.
                    None => prev_name_elem = None,
                }
            }
        }

        // 4. Render citations with locator.
        // 4a. Make final calls on all [`SpeculativeCiteProperties`].
        //     - Re-check for ibid.
        for i in 0..res.len() {
            for j in 0..res[i].items.len() {
                // TODO filter is not hidden
                let last = if j == 0 && i == 0 {
                    None
                } else if j == 0 {
                    res[i - 1].items.last()
                } else {
                    Some(&res[i].items[j - 1])
                }
                .map(|l| CitationItem::with_locator(l.entry, l.locator.clone()));

                res[i].items[j].cite_props.speculative.ibid = IbidState::with_last(
                    &CitationItem::with_locator(
                        res[i].items[j].entry,
                        res[i].items[j].locator.clone(),
                    ),
                    last.as_ref(),
                );

                //     - Add final locator
                res[i].items[j].cite_props.speculative.locator =
                    res[i].items[j].locator.clone();
            }
        }

        //     - Determine final citation number if bibliography does not sort.
        if bib_style
            .csl
            .bibliography
            .as_ref()
            .and_then(|b| b.sort.as_ref())
            .is_none()
        {
            let mut seen: HashMap<*const T, usize> = HashMap::new();
            let mut start = self.citation_number_offset;
            for cite in res.iter_mut() {
                for item in cite.items.iter_mut() {
                    item.cite_props.speculative.citation_number =
                        *seen.entry(item.entry as _).or_insert_with(|| {
                            let num = start;
                            start += 1;
                            num
                        });
                }
            }
        }

        // 4b. Determine final note positions (first/subsequent/ibid/near-note).
        apply_note_positions(&mut res);

        // Rerender.
        let mut final_citations: Vec<RenderedCitation> = Vec::new();
        for cite in res.iter_mut() {
            let mut style_ctx = cite.request.style();
            style_ctx.name_registry = Some(&name_registry);
            // 5. Collapse grouped citations.
            if cite.request.items.iter().all(|c| c.purpose.is_none()) {
                collapse_items(cite);
            }

            for item in cite.items.iter_mut() {
                item.rendered = last_purpose_render(&style_ctx, item, cite.request);
            }

            // 6. Add affixes.
            let formatting = Formatting::default()
                .apply(cite.request.style.citation.layout.to_formatting());
            let marks = QuoteMarks::get(&style_ctx);
            let pull_punctuation = style_ctx.punctuation_in_quotes();

            final_citations.push(RenderedCitation {
                note_number: cite.request.note_number,
                citation: if cite.items.iter().all(|i| i.hidden) {
                    ElemChildren::new()
                } else {
                    let mut elem_children: Vec<ElemChild> = Vec::new();

                    if let Some(prefix) = cite.request.prefix() {
                        elem_children.push(ElemChild::Text(Formatted {
                            text: quotes::apply(prefix, &marks),
                            formatting,
                        }));
                    }

                    for (i, item) in cite.items.iter().enumerate() {
                        if item.hidden {
                            continue;
                        }

                        // An item that renders nothing is dropped entirely,
                        // including its preceding delimiter: citeproc-js
                        // attaches the splice delimiter only to non-empty
                        // cite buffers, while the layout affixes survive. A
                        // per-item prefix or suffix keeps the cite alive.
                        if !item.rendered.has_content()
                            && item.prefix.is_none()
                            && item.suffix.is_none()
                        {
                            continue;
                        }

                        if i != 0
                            && let Some(delim) = cite
                                .items
                                .get(i)
                                .and_then(|i: &SpeculativeItemRender<T>| i.delim_override)
                                .or(cite
                                    .request
                                    .style
                                    .citation
                                    .layout
                                    .delimiter
                                    .as_deref())
                            && let Some(delim) =
                                item_delimiter(&cite.items[i - 1], item, delim)
                        {
                            elem_children.push(ElemChild::Text(Formatted {
                                text: delim.to_string(),
                                formatting,
                            }));
                        }

                        if let Some(prefix) = &item.prefix {
                            elem_children.push(ElemChild::Text(Formatted {
                                text: quotes::apply(prefix, &marks),
                                formatting,
                            }));
                        }

                        elem_children.push(ElemChild::Elem(Elem {
                            children: item.rendered.clone(),
                            display: None,
                            meta: Some(ElemMeta::Entry(
                                item.cite_props.certain.initial_idx,
                            )),
                            formatting: Formatting::default(),
                        }));

                        if let Some(suffix) = &item.suffix {
                            let mut text = quotes::apply(suffix, &marks);
                            if pull_punctuation {
                                pull_leading_punctuation(
                                    &mut elem_children,
                                    &mut text,
                                    &marks,
                                );
                            }
                            elem_children
                                .push(ElemChild::Text(Formatted { text, formatting }));
                        }
                    }

                    if let Some(suffix) = cite.request.suffix() {
                        let mut text = quotes::apply(suffix, &marks);
                        if pull_punctuation {
                            pull_leading_punctuation(
                                &mut elem_children,
                                &mut text,
                                &marks,
                            );
                        }
                        let last = last_text_mut_child(&mut elem_children)
                            .map(|t| t.text.as_str());
                        if should_print_suffix(last, &text) {
                            elem_children.push(Formatted { text, formatting }.into());
                        }
                    }

                    let layout_affixes = cite.request.style.citation.layout.to_affixes();
                    if elem_children.is_empty()
                        && cite.items.len() == 1
                        && cite.request.prefix().is_none()
                        && cite.request.suffix().is_none()
                        && layout_affixes.prefix.is_none()
                        && layout_affixes.suffix.is_none()
                    {
                        elem_children.push(ElemChild::Text(Formatted {
                            text: "[CSL STYLE ERROR: reference with no printed form.]"
                                .to_string(),
                            formatting,
                        }));
                    }

                    let mut children = simplify_children(ElemChildren(elem_children));
                    coalesce_text_runs(&mut children, formatting);
                    children
                },
            })
        }

        let mut bib_render = if let Some(bibliography) = &request.style.bibliography {
            let mut items = Vec::new();
            for (entry_idx, entry) in entries.into_iter().enumerate() {
                let cited_item = res
                    .iter()
                    .flat_map(|cite| cite.items.iter())
                    .find(|item| item.entry == entry.entry)
                    .unwrap();

                // A sorted bibliography numbers its entries by the final
                // bibliography order. Citations carry the lazy per-citation
                // numbers from step 1, so the entry's number must be set
                // explicitly here.
                let mut speculative =
                    cited_item.cite_props.speculative.for_bibliography();
                if bibliography_sorts {
                    speculative.citation_number = self.citation_number_offset + entry_idx;
                }

                let rendered_entry = simplify_children(
                    bib_style
                        .bibliography(
                            entry.entry,
                            CiteProperties {
                                certain: cited_item.cite_props.certain,
                                speculative,
                            },
                            cited_item.locale.as_ref(),
                            request.locale.as_ref(),
                        )
                        .unwrap(),
                );
                items.push((rendered_entry, entry.entry.key().to_string()));
            }

            substitute_subsequent_authors(
                bibliography.subsequent_author_substitute.as_ref(),
                bibliography.subsequent_author_substitute_rule,
                &mut items,
            );

            // citeproc-js drops bibliography entries with no printed form,
            // except in numeric bibliographies, where the number must stay
            // and the entry body shows the style-error placeholder.
            let entry_formatting =
                Formatting::default().apply(bibliography.layout.to_formatting());
            let uses_citation_number =
                format!("{:?}", bibliography.layout).contains("CitationNumber");
            let second_field = bibliography.second_field_align.is_some();
            let mut entry_number = self.citation_number_offset;
            items.retain_mut(|(content, _)| {
                let number = entry_number + 1;
                entry_number += 1;
                if content.has_content() {
                    return true;
                }
                if second_field {
                    content.0.push(
                        Formatted {
                            text: "[CSL STYLE ERROR: reference with no printed form.]"
                                .to_string(),
                            formatting: entry_formatting,
                        }
                        .into(),
                    );
                    true
                } else if uses_citation_number {
                    content.0.push(
                        Formatted {
                            text: format!(
                                "{number}. [CSL STYLE ERROR: reference with no printed form.]"
                            ),
                            formatting: entry_formatting,
                        }
                        .into(),
                    );
                    true
                } else {
                    false
                }
            });

            // The bibliography layout's formatting is applied around the whole
            // entry (including the second-field-align field divs) by
            // serializers, mirroring citeproc-js.
            Some(RenderedBibliography {
                hanging_indent: bibliography.hanging_indent,
                second_field_align: bibliography.second_field_align,
                line_spacing: bibliography.line_spacing,
                entry_spacing: bibliography.entry_spacing,
                items: items
                    .into_iter()
                    .map(|(mut i, key)| {
                        if bibliography.second_field_align.is_some() {
                            let first_field = i.remove_any_meta();
                            // citeproc-js keeps the right-inline content
                            // free of trailing whitespace: the last
                            // element's suffix whitespace migrates out of
                            // the block (F-117).
                            trim_trailing_whitespace(&mut i);
                            BibliographyItem::new(key, first_field, entry_formatting, i)
                        } else {
                            BibliographyItem::new(key, None, entry_formatting, i)
                        }
                    })
                    .collect(),
            })
        } else {
            None
        };

        // Coalesce equal-formatting text runs across inline containers so
        // that serializers produce one formatting tag per run, matching
        // citeproc-js. Only leaves inheriting the layout formatting join a
        // run; separately declared formatting keeps its own tag pair.
        if let Some(bibliography) = &request.style.bibliography {
            let ambient =
                Formatting::default().apply(bibliography.layout.to_formatting());
            if let Some(bib) = &mut bib_render {
                for item in &mut bib.items {
                    coalesce_text_runs(&mut item.content, ambient);
                    if let Some(ElemChild::Elem(field)) = &mut item.first_field {
                        coalesce_text_runs(&mut field.children, ambient);
                    }
                }
            }
        }

        if let Some(bib) = &mut bib_render {
            for item in &mut bib.items {
                strip_empty_displays(&mut item.content);
            }
        }
        for citation in &mut final_citations {
            strip_empty_displays(&mut citation.citation);
        }

        Rendered {
            bibliography: bib_render,
            citations: final_citations,
        }
    }
}

/// Create a new citation with the given items. Bibliography-wide disambiguation
/// and some other features will not be applied.
pub fn standalone_citation<T: EntryLike>(
    mut req: CitationRequest<'_, T>,
) -> ElemChildren {
    let style = req.style();
    style.sort(
        &mut req.items,
        style.csl.citation.sort.as_ref(),
        req.locale.as_ref(),
        |_| 0,
    );
    let mut res = vec![];
    let mut all_hidden = true;
    for item in req.items {
        if item.hidden {
            continue;
        } else {
            all_hidden = false;
        }

        res.push(if let Some(CitePurpose::Year) = item.purpose {
            date_replacement(
                &style,
                item.entry,
                &CiteProperties::for_sorting(item.locator, 0),
                req.locale.as_ref(),
                item.locale.as_ref(),
            )
        } else {
            style.citation(
                item.entry,
                CiteProperties::for_sorting(item.locator, 0),
                item.locale.as_ref(),
                req.locale.as_ref(),
                item.purpose,
                None,
                item.prefix.as_deref(),
            )
        });
    }

    let non_empty: Vec<_> = res.into_iter().filter(|c| c.has_content()).collect();

    let formatting =
        Formatting::default().apply(style.csl.citation.layout.to_formatting());
    let marks = QuoteMarks::get(&style);
    let pull_punctuation = style.punctuation_in_quotes();

    if !non_empty.is_empty() && !all_hidden {
        let mut res = if let Some(prefix) = style.csl.citation.layout.prefix.as_ref() {
            ElemChildren(vec![
                Formatted { text: quotes::apply(prefix, &marks), formatting }.into(),
            ])
        } else {
            ElemChildren::new()
        };

        for (i, elem_children) in non_empty.into_iter().enumerate() {
            let first = i == 0;
            if !first {
                res.0.push(
                    Formatted {
                        text: style
                            .csl
                            .citation
                            .layout
                            .delimiter
                            .as_deref()
                            .unwrap_or(Citation::DEFAULT_CITE_GROUP_DELIMITER)
                            .to_string(),
                        formatting,
                    }
                    .into(),
                );
            }

            res.0.extend(elem_children.0)
        }

        if let Some(suffix) = style.csl.citation.layout.suffix.as_ref() {
            let mut text = quotes::apply(suffix, &marks);
            if pull_punctuation {
                pull_leading_punctuation(&mut res.0, &mut text, &marks);
            }
            let last = res.last_text().map(|t| t.text.as_str());
            if should_print_suffix(last, &text) {
                res.0.push(Formatted { text, formatting }.into());
            }
        }

        let mut res = simplify_children(res);
        coalesce_text_runs(&mut res, formatting);
        res
    } else {
        ElemChildren::new()
    }
}

fn do_rerender<T: EntryLike>(
    ctx: &StyleContext<'_>,
    item: &SpeculativeItemRender<T>,
    request: &CitationRequest<'_, T>,
) -> ElemChildren {
    ctx.citation(
        item.entry,
        item.cite_props.clone(),
        item.locale.as_ref(),
        request.locale.as_ref(),
        item.purpose,
        item.collapse_verdict,
        item.prefix.as_deref(),
    )
}

/// Render an item the way citeproc-js scans for ambiguity.
///
/// `CSL.getAmbiguousCite` forces `position: subsequent` and `near-note: true`
/// on the cited item, and passes neither locator nor affixes. This differs
/// from the actual citation whenever the style branches on `position`.
fn ambiguity_render<T: EntryLike>(
    ctx: &StyleContext<'_>,
    entry: &T,
    cite_props: &CiteProperties<'_>,
    locale: Option<&LocaleCode>,
    purpose: Option<CitePurpose>,
    request: &CitationRequest<'_, T>,
) -> ElemChildren {
    scan_render(ctx, entry, cite_props, locale, purpose, request, None).0
}

/// Like [`ambiguity_render`], but with a forced disambiguation state and also
/// returning the properties of the first names element of the scan render.
///
/// citeproc-js scans disambiguation candidates with the names already expanded
/// to their maximum, because the `disNames` counter is forward-only and keeps
/// its value even when a step did not improve the visible render.
fn scan_render<T: EntryLike>(
    ctx: &StyleContext<'_>,
    entry: &T,
    cite_props: &CiteProperties<'_>,
    locale: Option<&LocaleCode>,
    purpose: Option<CitePurpose>,
    request: &CitationRequest<'_, T>,
    state: Option<DisambiguateState>,
) -> (ElemChildren, Option<NameDisambiguationProperties>) {
    let mut props = cite_props.clone();
    props.certain.position = Some(CitePosition::Subsequent);
    props.certain.near_note = Some(true);
    props.certain.is_near_note = true;
    props.speculative.ibid = IbidState::Different;
    props.speculative.locator = None;
    if let Some(state) = state {
        props.speculative.disambiguation = state;
    }
    let ctx = ctx.do_citation(
        entry,
        props,
        locale,
        request.locale.as_ref(),
        purpose,
        None,
        None,
    );
    let first_name = ctx.writing.first_name.clone();
    (ctx.flush(), first_name)
}

fn date_replacement<T: EntryLike>(
    ctx: &StyleContext<'_>,
    entry: &T,
    cite_props: &CiteProperties,
    term_locale: Option<&LocaleCode>,
    locale: Option<&LocaleCode>,
) -> ElemChildren {
    let date = entry
        .resolve_date_variable(DateVariable::Issued)
        .or_else(|| entry.resolve_date_variable(DateVariable::EventDate))
        .or_else(|| entry.resolve_date_variable(DateVariable::Submitted))
        .or_else(|| entry.resolve_date_variable(DateVariable::OriginalDate));

    ElemChildren(vec![ElemChild::Text(Formatted {
        text: if let Some(date) = date {
            let mut s = String::with_capacity(4);
            let c = ctx.ctx(entry, cite_props.clone(), locale, term_locale, false, None);
            let ad = c
                .term(Term::Other(OtherTerm::Ad), TermForm::default(), false)
                .unwrap_or(" AD");
            let bc = c
                .term(Term::Other(OtherTerm::Bc), TermForm::default(), false)
                .unwrap_or(" BC");
            write_year(date.year, false, &mut s, ad, bc).unwrap();
            s
        } else if let Some(no_date) = ctx
            .ctx(entry, cite_props.clone(), locale, term_locale, false, None)
            .term(Term::Other(OtherTerm::NoDate), TermForm::default(), false)
        {
            no_date.to_string()
        } else {
            "n.d.".to_string()
        },
        formatting: Formatting::default(),
    })])
}

pub fn write_year<W: std::fmt::Write>(
    year: i32,
    short: bool,
    w: &mut W,
    ad: &str,
    bc: &str,
) -> std::fmt::Result {
    if short && year >= 1000 {
        return write!(w, "{:02}", year % 100);
    }

    write!(
        w,
        "{}{}",
        if year > 0 { year } else { year.abs() + 1 },
        if year < 1000 {
            if year <= 0 {
                bc
            } else {
                // AD is used as a postfix, see
                // https://docs.citationstyles.org/en/stable/specification.html?#ad-and-bc
                ad
            }
        } else {
            ""
        }
    )
}

fn last_purpose_render<T: EntryLike + Debug>(
    ctx: &StyleContext<'_>,
    item: &SpeculativeItemRender<T>,
    request: &CitationRequest<'_, T>,
) -> ElemChildren {
    if let Some(CitePurpose::Year) = item.purpose {
        date_replacement(
            ctx,
            item.entry,
            &item.cite_props,
            request.locale.as_ref(),
            item.locale.as_ref(),
        )
    } else {
        do_rerender(ctx, item, request)
    }
}

/// The text of a rendered item as used for ambiguity detection.
///
/// citeproc-js compares the plain (undecorated) cite text but suppresses the
/// `accessed` date while looking for ambiguity, because two cites that differ
/// only in their access date are still ambiguous for disambiguation purposes
/// (`date_YearSuffixWithNoDate`).
fn ambiguity_key(children: &ElemChildren) -> String {
    fn helper(children: &ElemChildren, out: &mut String) {
        for child in &children.0 {
            match child {
                ElemChild::Text(text) => out.push_str(&text.text),
                ElemChild::Link { text, .. } => out.push_str(&text.text),
                ElemChild::Elem(elem) => {
                    if elem.meta == Some(ElemMeta::AccessedDate) {
                        continue;
                    }
                    helper(&elem.children, out);
                }
                ElemChild::Markup(markup) => out.push_str(markup),
                ElemChild::Transparent { .. } => {}
            }
        }
    }

    let mut out = String::new();
    helper(children, &mut out);
    out
}

type AmbiguousGroup = Vec<(usize, usize)>;

/// Get all names in `children`.
///
/// **NOTE**: These not just the rendered names, but all names where the corresponding variable occurs.
fn get_names(children: &ElemChildren) -> Vec<Person> {
    fn helper(children: &ElemChildren, persons: &mut Vec<Person>) {
        for c in &children.0 {
            if let ElemChild::Elem(e) = c {
                if let Some(ElemMeta::Names(ns)) = &e.meta {
                    persons.extend(ns.iter().flat_map(|(ps, _)| ps).cloned());
                }
                helper(&e.children, persons);
            }
        }
    }
    let mut res = vec![];
    helper(children, &mut res);
    res
}

#[derive(Debug)]
/// A state used for disambiguation.
struct DisambData<'a, T: EntryLike + Debug> {
    /// The citation index of the item.
    cite_id: usize,
    /// The item index.
    item_id: usize,
    /// Names occurring in this citation item.
    names: Vec<Person>,
    /// The related speculative render
    item: &'a SpeculativeItemRender<'a, T>,
}

impl<'a, T: EntryLike + Debug> PartialEq for DisambData<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.cite_id == other.cite_id && self.item_id == other.item_id
    }
}

impl<'a, T: EntryLike + Debug> Eq for DisambData<'a, T> {}

/// Document-wide registry of rendered names, mirroring citeproc-js's
/// `CSL.NameRegister`.
///
/// Given-name disambiguation for the non-`by-cite` rules is not scoped to an
/// ambiguity group: citeproc-js counts distinct initials and full given names
/// per family name across the whole document and expands every matching name.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct NameRegistry {
    /// Family name → initials → full given names.
    families: HashMap<String, HashMap<String, HashSet<String>>>,
}

impl NameRegistry {
    fn register(&mut self, person: &Person) {
        if person.name.is_empty() || person.given_name.is_none() {
            return;
        }
        let family = family_key(person).replace('.', " ");
        let family = family.trim().to_string();
        if family.is_empty() {
            return;
        }
        let mut initials = String::new();
        person.initials(&mut initials, None, false).ok();
        let initials: String =
            initials.chars().filter(|c| !c.is_whitespace() && *c != '.').collect();
        let given = person
            .given_name
            .as_deref()
            .unwrap_or_default()
            .replace('.', " ")
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        self.families
            .entry(family)
            .or_default()
            .entry(initials)
            .or_default()
            .insert(given);
    }

    /// `(distinct initials, distinct full given names)` for the family name.
    fn counts(&self, person: &Person) -> (usize, usize) {
        let family = family_key(person).replace('.', " ");
        let Some(by_initials) = self.families.get(family.trim()) else {
            return (0, 0);
        };
        let mut buf = String::new();
        person.initials(&mut buf, None, false).ok();
        let initials_key: String =
            buf.chars().filter(|c| !c.is_whitespace() && *c != '.').collect();
        let given_count =
            by_initials.get(&initials_key).map(HashSet::len).unwrap_or_default();
        (by_initials.len(), given_count)
    }
}

/// The family name including an explicit non-dropping particle: `dos
/// Santos` and `Santos` are different families for disambiguation.
fn family_key(person: &Person) -> String {
    if let Some(particle) = &person.non_dropping_particle {
        format!("{particle} {}", person.name)
    } else {
        person.name.clone()
    }
}

/// The rendered name list of an item as it participates in disambiguation.
///
/// Two items can only be disambiguated by their names when this key differs;
/// it mirrors what `add_names` would print (visible count, family names, and
/// the given-name form for each visible name).
fn name_disambiguation_key(
    props: &NameDisambiguationProperties,
    names: &[Person],
) -> String {
    let count = props.visible_count();
    let mut key = format!("{count}\u{1e}");
    for (idx, person) in names.iter().enumerate().take(count) {
        key.push_str(&family_key(person));
        key.push('\u{1f}');
        match props.form_at(idx) {
            Some(DisambiguatedNameForm::LongInitialized) => {
                let mut initials = String::new();
                person.initials(&mut initials, None, false).ok();
                key.push_str(&initials);
            }
            Some(DisambiguatedNameForm::LongFull) => {
                key.push_str(person.given_name.as_deref().unwrap_or_default());
            }
            _ => {}
        }
        key.push('\u{1e}');
    }
    // A truncated list renders an et-al marker, which distinguishes it from a
    // list that happens to end at the same number of names
    // (`disambiguate_YearSuffixAtTwoLevels`).
    if props.name_count() > count {
        key.push_str("et-al");
    }
    key
}

/// Compute the target given-name form for a name that has to be disambiguated.
fn disambiguated_form_target(
    base: DisambiguatedNameForm,
    needs_full: bool,
    with_initials_only: bool,
) -> DisambiguatedNameForm {
    if base == DisambiguatedNameForm::Count || base == DisambiguatedNameForm::LongFull {
        return base;
    }
    if with_initials_only {
        // The rule cannot render full given names, so a collision of initials
        // is not disambiguated at all (`disambiguate_ToInitialOnly`).
        if needs_full {
            return base;
        }
        return match base {
            DisambiguatedNameForm::ShortInitialized => {
                DisambiguatedNameForm::LongInitialized
            }
            other => other,
        };
    }
    if needs_full {
        return DisambiguatedNameForm::LongFull;
    }
    match base {
        DisambiguatedNameForm::ShortInitialized
        | DisambiguatedNameForm::LongInitialized => {
            DisambiguatedNameForm::LongInitialized
        }
        // No `initialize-with` is set, so initials cannot be rendered: expand
        // to the full given name (`disambiguate_AllNamesSimpleSequence`).
        DisambiguatedNameForm::ShortFull => DisambiguatedNameForm::LongFull,
        other => other,
    }
}

/// Expand given names of the group members in `active` where their family
/// names clash but their given names differ.
///
/// `rule` selects which names may be expanded (`primary-name*` rules only
/// touch the first name) and whether only initials may be added
/// (`*-with-initials`). Matching citeproc-js, an initial is used when it is
/// unique among the clashing names and the full given name otherwise.
fn expand_given_names<T: EntryLike + Debug>(
    data: &[DisambData<'_, T>],
    props: &mut [Option<NameDisambiguationProperties>],
    active: &[usize],
    rule: DisambiguationRule,
) {
    let with_initials_only = matches!(
        rule,
        DisambiguationRule::AllNamesWithInitials
            | DisambiguationRule::PrimaryNameWithInitials
    );
    let primary_only = matches!(
        rule,
        DisambiguationRule::PrimaryName | DisambiguationRule::PrimaryNameWithInitials
    );

    let max_names = active
        .iter()
        .filter_map(|idx| {
            props[*idx].as_ref().map(NameDisambiguationProperties::visible_count)
        })
        .max()
        .unwrap_or_default();

    for pos in 0..max_names {
        if primary_only && pos > 0 {
            break;
        }

        let visible: Vec<usize> = active
            .iter()
            .copied()
            .filter(|idx| {
                props[*idx].as_ref().is_some_and(|p| p.form_at(pos).is_some())
                    && data[*idx].names.get(pos).is_some()
            })
            .collect();
        if visible.len() < 2 {
            continue;
        }

        let mut needs_initial = HashSet::new();
        let mut needs_full = HashSet::new();
        for (i, a) in visible.iter().enumerate() {
            for b in &visible[i + 1..] {
                let pa = &data[*a].names[pos];
                let pb = &data[*b].names[pos];
                if pa.name != pb.name {
                    continue;
                }
                let (Some(given_a), Some(given_b)) = (&pa.given_name, &pb.given_name)
                else {
                    continue;
                };
                if given_a == given_b {
                    continue;
                }
                let mut initials_a = String::new();
                pa.initials(&mut initials_a, None, false).ok();
                let mut initials_b = String::new();
                pb.initials(&mut initials_b, None, false).ok();
                needs_initial.insert(*a);
                needs_initial.insert(*b);
                if initials_a == initials_b {
                    needs_full.insert(*a);
                    needs_full.insert(*b);
                }
            }
        }

        for idx in needs_initial {
            let Some(props) = props[idx].as_mut() else { continue };
            let Some(base) = props.form_at(pos) else { continue };
            let target = disambiguated_form_target(
                base,
                needs_full.contains(&idx),
                with_initials_only,
            );
            props.set_form_at(pos, target);
        }
    }
}

/// Progressively transform names to disambiguate them.
///
/// This mirrors citeproc-js's sweep-based `disNames`: all still-ambiguous
/// entries grow one visible name per round, entries that become unique are
/// frozen at that count, and given-name expansion is recomputed after every
/// round so newly visible names can be expanded too.
fn disambiguate_names<F, T>(
    renders: &[SpeculativeCiteRender<'_, '_, T>],
    group: &AmbiguousGroup,
    mut mark: F,
) where
    T: EntryLike + Eq + Hash + Debug,
    F: FnMut(&T, DisambiguateState),
{
    let data = group
        .iter()
        .map(|(cite_id, item_id)| {
            let cite_id = *cite_id;
            let item_id = *item_id;
            let item = &renders[cite_id].items[item_id];
            DisambData {
                cite_id,
                item_id,
                names: get_names(&item.rendered),
                item,
            }
        })
        .collect::<Vec<_>>();

    let style = renders[data[0].cite_id].request.style;
    let add_names = style.citation.disambiguate_add_names;
    let rule = style
        .citation
        .disambiguate_add_givenname
        .then_some(style.citation.givenname_disambiguation_rule);

    // The disambiguation state in force for each group member, if it renders
    // a names element at all.
    let mut props: Vec<Option<NameDisambiguationProperties>> = data
        .iter()
        .map(|d| match &d.item.cite_props.speculative.disambiguation {
            DisambiguateState::NameDisambiguation(p) => Some(p.clone()),
            _ => d.item.first_name.clone(),
        })
        .collect();
    let original = props.clone();

    if rule.is_none() && !add_names {
        return;
    }

    let mut active: Vec<usize> = (0..data.len())
        .filter(|idx| props[*idx].is_some())
        .filter(|idx| {
            data[*idx]
                .item
                .cite_props
                .speculative
                .disambiguation
                .may_disambiguate_names()
        })
        .collect();

    // citeproc-js partitions the ambiguous set on every name-expansion step:
    // items whose render key differs from the probe item leave the current
    // list (they are already distinguishable from it) while the items that
    // still clash keep growing. A step is only kept when it refines that
    // partition, so increments that do not separate anything are discarded
    // when the list dies.
    //
    // The previous implementation counted items that still had *any* partner;
    // that misses the two-level case (`disambiguate_YearSuffixAtTwoLevels`):
    // expanding to three names splits a four-item group into two pairs, but
    // every item still has a partner, so the improvement was discarded and
    // the whole group fell through to year-suffix (a–d) without name
    // expansion.
    let mut best = props.clone();
    let mut best_partitions = 1usize;
    loop {
        if let Some(rule) = rule {
            expand_given_names(&data, &mut props, &active, rule);
        }

        let keys: Vec<String> = active
            .iter()
            .map(|idx| {
                name_disambiguation_key(props[*idx].as_ref().unwrap(), &data[*idx].names)
            })
            .collect();

        // Group positions in `active` by identical render key.
        let mut classes: Vec<Vec<usize>> = Vec::new();
        for (pos, key) in keys.iter().enumerate() {
            if let Some(class) = classes.iter_mut().find(|c| keys[c[0]] == *key) {
                class.push(pos);
            } else {
                classes.push(vec![pos]);
            }
        }

        if classes.len() > best_partitions {
            best_partitions = classes.len();
            best = props.clone();
        }

        let ambiguous: Vec<usize> = classes
            .iter()
            .filter(|class| class.len() > 1)
            .flat_map(|class| class.iter().map(|pos| active[*pos]))
            .collect();

        if ambiguous.is_empty() || !add_names {
            if ambiguous.is_empty() {
                best = props.clone();
            }
            break;
        }

        let mut grew = false;
        for idx in &ambiguous {
            let Some(props) = props[*idx].as_mut() else { continue };
            let visible = props.visible_count();
            if visible < props.name_count() {
                props.add_name(visible + 1);
                grew = true;
            }
        }
        if !grew {
            break;
        }
        active = ambiguous;
    }

    for (idx, props) in best.iter().enumerate() {
        let Some(props) = props else { continue };
        if original[idx].as_ref() == Some(props) {
            continue;
        }
        mark(data[idx].item.entry, DisambiguateState::NameDisambiguation(props.clone()));
    }
}

/// Count the `disambiguate="true"` conditions in the citation layout.
fn style_disambiguate_levels(csl: &IndependentStyle) -> u8 {
    fn helper(e: &LayoutRenderingElement, style: &StyleContext, count: &mut u8) {
        use citationberg::TextTarget;
        if let LayoutRenderingElement::Choose(choose) = e {
            for branch in choose.branches() {
                if branch.disambiguate == Some(true) {
                    *count = count.saturating_add(1);
                }
            }
            for branch in choose.branches() {
                for child in &branch.children {
                    helper(child, style, count);
                }
            }
            if let Some(otherwise) = &choose.otherwise {
                for child in &otherwise.children {
                    helper(child, style, count);
                }
            }
            return;
        }
        match e {
            LayoutRenderingElement::Text(Text {
                target: TextTarget::Macro { name },
                ..
            }) => {
                if let Some(mac) = style.get_macro(name) {
                    for child in &mac.children {
                        helper(child, style, count);
                    }
                }
            }
            LayoutRenderingElement::Group(Group { children, .. }) => {
                for child in children {
                    helper(child, style, count);
                }
            }
            _ => {}
        }
    }

    let style = StyleContext::new(csl, None, &[]);
    let mut count = 0;
    for element in &csl.citation.layout.elements {
        helper(element, &style, &mut count);
    }
    count
}

/// Expand the names of a [`NameDisambiguationProperties`] to the maximum
/// form the style can render.
fn maximal_name_props(
    mut props: NameDisambiguationProperties,
) -> NameDisambiguationProperties {
    let count = props.name_count();
    let visible = props.visible_count();
    if visible < count {
        props.add_name(count);
    }
    for idx in 0..count {
        let Some(mut form) = props.form_at(idx) else { continue };
        while let Some(next) = form.disambiguate(true) {
            form = next;
        }
        props.set_form_at(idx, form);
    }
    props
}

/// Mark qualifying entries for disambiguation with `cs:choose`.
///
/// Every member of an ambiguous group activates the next `disambiguate`
/// level, matching citeproc-js: the first level is enabled for all clashing
/// entries (including the first), and entries that remain ambiguous after a
/// re-render activate the following level on the next sweep.
///
/// If the level makes the group unique once the names element is expanded to
/// its maximum, the group is resolved at that level and the entries are
/// recorded in `resolved`: citeproc-js scanned this level with its
/// forward-only name counter at the maximum and committed only the
/// `disambiguate` level (`bugreports_EnvAndUrb`).
fn disambiguate_with_choose<F, T>(
    renders: &[SpeculativeCiteRender<'_, '_, T>],
    group: &AmbiguousGroup,
    mut mark: F,
    resolved: &mut HashSet<*const T>,
) where
    T: EntryLike,
    F: FnMut(&T, DisambiguateState),
{
    let style = renders[group[0].0].request.style;
    let max_level = style_disambiguate_levels(style);
    if max_level == 0 {
        return;
    }

    // One candidate level per entry (the maximum over its occurrences).
    let mut levels: Vec<(&T, u8)> = Vec::new();
    for &(cite_idx, item_idx) in group.iter() {
        let item = &renders[cite_idx].items[item_idx];
        if !item.checked_disambiguate
            || !item
                .cite_props
                .speculative
                .disambiguation
                .may_disambiguate_with_choose()
        {
            continue;
        }
        let current = match item.cite_props.speculative.disambiguation {
            DisambiguateState::Choose(level) => level,
            _ => 0,
        };
        if current >= max_level {
            continue;
        }
        let next = current + 1;
        match levels.iter_mut().find(|(entry, _)| std::ptr::eq(*entry, item.entry)) {
            Some(slot) => slot.1 = slot.1.max(next),
            None => levels.push((item.entry, next)),
        }
    }
    if levels.is_empty() {
        return;
    }

    // Trial scan: render each entry at its candidate level with the names
    // expanded to the maximum. If every entry is distinct, the level
    // resolves the ambiguity as far as citeproc-js is concerned.
    let mut trial_keys = Vec::with_capacity(levels.len());
    let mut all_named = true;
    for (entry, level) in &levels {
        let Some(&(cite_idx, item_idx)) = group
            .iter()
            .find(|(cite_idx, item_idx)| {
                std::ptr::eq(renders[*cite_idx].items[*item_idx].entry, *entry)
            })
        else {
            all_named = false;
            break;
        };
        let item = &renders[cite_idx].items[item_idx];
        let style_ctx = renders[cite_idx].request.style();
        let (children, props) = scan_render(
            &style_ctx,
            item.entry,
            &item.cite_props,
            item.locale.as_ref(),
            item.purpose,
            &renders[cite_idx].request,
            Some(DisambiguateState::Choose(*level)),
        );
        match props {
            Some(props) => trial_keys
                .push(name_disambiguation_key(&maximal_name_props(props), &get_names(&children))),
            None => {
                all_named = false;
                break;
            }
        }
    }
    let trial_resolved = all_named && {
        let distinct: HashSet<&String> = trial_keys.iter().collect();
        distinct.len() == trial_keys.len()
    };

    for (entry, level) in levels {
        mark(entry, DisambiguateState::Choose(level));
        if trial_resolved {
            resolved.insert(entry as *const T);
        }
    }
}

/// Mark qualifying entries for disambiguation with year suffixes.
fn disambiguate_year_suffix<F, T>(
    renders: &[SpeculativeCiteRender<'_, '_, T>],
    group: &AmbiguousGroup,
    bib_rank: &HashMap<*const T, usize>,
    mut mark: F,
) where
    T: EntryLike + PartialEq,
    F: FnMut(&T, u8),
{
    if renders.iter().flat_map(|r| r.items.iter()).any(|i| {
        if i.style_uses_year_suffix_var {
            return true;
        }

        let entry_has_date = i
            .entry
            .resolve_date_variable(DateVariable::Issued)
            .or_else(|| i.entry.resolve_date_variable(DateVariable::Accessed))
            .or_else(|| i.entry.resolve_date_variable(DateVariable::AvailableDate))
            .or_else(|| i.entry.resolve_date_variable(DateVariable::EventDate))
            .or_else(|| i.entry.resolve_date_variable(DateVariable::Submitted))
            .or_else(|| i.entry.resolve_date_variable(DateVariable::OriginalDate))
            .is_some();

        i.rendered
            .find_elem_by(&|e| {
                // The citation label will contain the date if there is one.
                e.meta == Some(ElemMeta::Date)
                    || (entry_has_date && e.meta == Some(ElemMeta::CitationLabel))
            })
            .is_some()
    }) && group.iter().any(|&(cite_idx, item_idx)| {
        renders[cite_idx].request.style.citation.disambiguate_add_year_suffix
            && renders[cite_idx].items[item_idx]
                .cite_props
                .speculative
                .year_suffix
                .is_none()
    }) {
        let mut entries = Vec::new();
        for &(cite_idx, item_idx) in group.iter() {
            let item = &renders[cite_idx].items[item_idx];
            if item.cite_props.speculative.year_suffix.is_none()
                && !entries.contains(&item.entry)
            {
                entries.push(item.entry);
            }
        }

        // Assign year suffixes in bibliography order.
        entries.sort_by_key(|entry| {
            bib_rank.get(&(*entry as *const T)).copied().unwrap_or(usize::MAX)
        });
        for (i, entry) in entries.into_iter().enumerate() {
            mark(entry, i as u8);
        }
    }
}

/// Return a vector that contains every group of mutually ambiguous items with
/// cite and item index.
fn find_ambiguous_sets<T: EntryLike + PartialEq>(
    cites: &[SpeculativeCiteRender<'_, '_, T>],
    resolved: &HashSet<*const T>,
) -> Vec<AmbiguousGroup> {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum PotentialDisambiguation {
        /// Two usizes for an item that produced this string.
        Single((usize, usize)),
        /// There were multiple matches. This is the index in the result vector.
        Match(usize),
    }

    let mut map: HashMap<String, PotentialDisambiguation> = HashMap::new();
    let mut res: Vec<Vec<(usize, usize)>> = Vec::new();

    for (i, cite) in cites.iter().enumerate() {
        for (j, item) in cite.items.iter().enumerate() {
            if item.cite_props.speculative.year_suffix.is_some()
                || resolved.contains(&(item.entry as *const T))
            {
                // This item already carries a suffix, or a
                // `disambiguate="true"` level was found to resolve it.
                continue;
            }

            let buf = ambiguity_key(&item.ambiguity_rendered);
            match map.entry(buf) {
                HmEntry::Occupied(entry) => match *entry.get() {
                    PotentialDisambiguation::Single(pos) => {
                        *entry.into_mut() = PotentialDisambiguation::Match(res.len());
                        res.push(vec![pos, (i, j)]);
                    }
                    PotentialDisambiguation::Match(idx) => {
                        res[idx].push((i, j));
                    }
                },
                HmEntry::Vacant(vacant) => {
                    vacant.insert(PotentialDisambiguation::Single((i, j)));
                }
            }
        }
    }

    // Only return items if not every item points to the same entry.
    res.into_iter()
        .filter(|e| {
            let Some(first_entry) =
                e.first().map(|(cite, item)| cites[*cite].items[*item].entry)
            else {
                return false;
            };

            e.iter()
                .any(|(cite, item)| cites[*cite].items[*item].entry != first_entry)
        })
        .collect()
}

/// Render an element's plain text (used for citeproc's `authorstring`).
fn plain_elem(e: &Elem) -> String {
    let mut out = String::new();
    e.write_buf(&mut out, BufWriteFormat::Plain).unwrap();
    out
}

/// Move a leading period/comma of a suffix inside a trailing closing quote
/// when the locale enables punctuation-in-quote.
fn move_punctuation_inside_quote(
    children: &mut ElemChildren,
    suffix: &mut String,
    enabled: bool,
    marks: &QuoteMarks,
) {
    if !enabled {
        return;
    }
    let Some(first) = suffix.chars().next() else { return };
    if first != '.' && first != ',' {
        return;
    }
    let Some(last) = last_text_mut_child(&mut children.0) else { return };
    // Insert before the whole trailing run of closing marks: a title that
    // ends in nested quotes keeps the punctuation inside all of them
    // (`2015.’”`, `bugreports_NoCaseEscape`).
    if quotes::move_punctuation_inside(&mut last.text, first, marks) {
        suffix.drain(..first.len_utf8());
    }
}

/// Collect the rendered text of all `cs:name` elements below `e`.
fn collect_name_text(e: &Elem, out: &mut String) {
    if matches!(e.meta, Some(ElemMeta::Name(_, _))) {
        out.push_str(&plain_elem(e));
    } else {
        for child in &e.children.0 {
            if let ElemChild::Elem(child) = child {
                collect_name_text(child, out);
            }
        }
    }
}

/// A cite-grouping key from a names element: the names without the label, so
/// that `Doe, John ed.` and `Doe, John` are the same author.
fn names_key(e: &Elem) -> String {
    let mut out = String::new();
    collect_name_text(e, &mut out);
    out
}

/// Fallback author string for styles whose citation layout renders no
/// `<names>` element but still groups/collapses cites.
fn entry_author_key<T: EntryLike>(entry: &T) -> String {
    let author = entry.resolve_name_variable(NameVariable::Author);
    let people = if author.is_empty() {
        entry.resolve_name_variable(NameVariable::Editor)
    } else {
        author
    };
    let mut out = String::new();
    for (i, person) in people.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        out.push_str(&person.name);
        out.push(' ');
        if let Some(given) = &person.given_name {
            out.push_str(given);
        }
    }
    out
}

/// Recursively remove display elements that render nothing: citeproc-js does
/// not emit an empty `csl-block`/`csl-right-inline` div.
fn strip_empty_displays(children: &mut ElemChildren) {
    children.0.retain_mut(|child| match child {
        ElemChild::Elem(e) => {
            strip_empty_displays(&mut e.children);
            !(e.display.is_some() && !e.has_content_visible())
        }
        _ => true,
    });
}

/// Compute citeproc-js's position state with note awareness.
///
/// Citeproc evaluates in-text (`noteIndex == 0`) and note citations as two
/// independent sequences, considers separate citations in the same note for
/// ibid, and suppresses cross-note ibid when the previous note held more than
/// one citation. The initial speculative render cannot know this; the final
/// render uses the result.
fn apply_note_positions<T: EntryLike + PartialEq>(
    cites: &mut [SpeculativeCiteRender<'_, '_, T>],
) {
    let note_numbers: Vec<Option<usize>> =
        cites.iter().map(|c| c.request.note_number).collect();
    // citeproc-js counts *items* (not citation clusters) per note; a note
    // with two cites in one cluster still blocks cross-note ibid.
    let mut note_counts: HashMap<usize, usize> = HashMap::new();
    for (i, note) in note_numbers.iter().enumerate() {
        if let Some(note) = note {
            *note_counts.entry(*note).or_default() += cites[i].items.len();
        }
    }

    for text_sequence in [true, false] {
        let indices: Vec<usize> = (0..cites.len())
            .filter(|&i| {
                let note = note_numbers[i].unwrap_or(0);
                (text_sequence && note == 0) || (!text_sequence && note != 0)
            })
            .collect();

        let mut first_ref: HashMap<*const T, usize> = HashMap::new();
        let mut last_ref: HashMap<*const T, usize> = HashMap::new();
        let mut prev_citation: Option<usize> = None;

        for &ci in &indices {
            let note = note_numbers[ci].unwrap_or(0);
            let near_distance =
                cites[ci].request.style.citation.near_note_distance as usize;
            let len = cites[ci].items.len();
            for k in 0..len {
                let entry_ptr = cites[ci].items[k].entry as *const T;
                let locator = cites[ci].items[k].locator.clone();
                let first = !first_ref.contains_key(&entry_ptr);

                let mut position = if first {
                    first_ref.insert(entry_ptr, note);
                    CitePosition::First
                } else {
                    CitePosition::Subsequent
                };

                if !first {
                    let mut ibidme = false;
                    let mut prev_locator: Option<SpecificLocator<'_>> = None;
                    if k > 0 {
                        let prev = &cites[ci].items[k - 1];
                        if prev.entry == cites[ci].items[k].entry {
                            ibidme = true;
                            prev_locator = prev.locator.clone();
                        }
                    } else if let Some(pi) = prev_citation {
                        let prev_note = note_numbers[pi].unwrap_or(0);
                        let prev_first = cites[pi].items.first();
                        let prev_last = cites[pi].items.last();
                        if prev_note == note {
                            if let Some(prev) = prev_last
                                && prev.entry == cites[ci].items[k].entry
                            {
                                ibidme = true;
                                prev_locator = prev.locator.clone();
                            }
                        } else if note > 0
                            && prev_note + 1 >= note
                            && note_counts.get(&prev_note).copied().unwrap_or(0) == 1
                            && let Some(prev) = prev_first
                            && prev.entry == cites[ci].items[k].entry
                        {
                            ibidme = true;
                            prev_locator = prev.locator.clone();
                        } else if note == 0
                            && let Some(prev) = prev_first
                            && prev.entry == cites[ci].items[k].entry
                        {
                            // In-text cites are all in "note 0", which
                            // citeproc treats as a single note.
                            ibidme = true;
                            prev_locator = prev.locator.clone();
                        }
                    }

                    if ibidme {
                        position = match (&prev_locator, &locator) {
                            (None, None) => CitePosition::Ibid,
                            (None, Some(_)) => CitePosition::IbidWithLocator,
                            (Some(_), None) => CitePosition::Subsequent,
                            (Some(a), Some(b)) if a == b => CitePosition::Ibid,
                            (Some(_), Some(_)) => CitePosition::IbidWithLocator,
                        };
                    }
                }

                let near = if position == CitePosition::First {
                    false
                } else if text_sequence {
                    true
                } else {
                    last_ref
                        .get(&entry_ptr)
                        .is_some_and(|last| note.saturating_sub(*last) <= near_distance)
                };
                last_ref.insert(entry_ptr, note);

                let first_note = first_ref.get(&entry_ptr).copied().unwrap_or(note);
                let item = &mut cites[ci].items[k];
                if item.cite_props.certain.position.is_none() {
                    item.cite_props.certain.position = Some(position);
                }
                if item.cite_props.certain.near_note.is_none() {
                    item.cite_props.certain.near_note = Some(near);
                }
                item.cite_props.certain.first_note_number = Some(first_note);
            }
            prev_citation = Some(ci);
        }
    }
}

/// Apply citeproc-js's grouped citation sort.
///
/// When a citation has a sort and collapses (or declares a cite-group
/// delimiter), conditions in an in-text style, cites are kept together by
/// their rendered author string. The group order is the first normal sort
/// key of the group (the internal name key when the key renders names), not
/// the author string itself, which is why `Smith 2003; Jones 2005; Smith 2010`
/// becomes `Smith 2003, 2010; Jones 2005`.
fn apply_grouped_sort<'a, T: EntryLike>(
    style: &StyleContext<'a>,
    cite: &mut SpeculativeCiteRender<'a, '_, T>,
    term_locale: Option<&LocaleCode>,
) {
    let citation = &style.csl.citation;
    if style.csl.settings.class != StyleClass::InText
        || (citation.collapse.is_none() && citation.cite_group_delimiter.is_none())
    {
        return;
    }
    let Some(sort) = citation.sort.as_ref() else { return };
    let Some(first_key) = sort.keys.first() else { return };

    // (authorstring, group-first-key, original item)
    let mut entries: Vec<(String, String, bool, SpeculativeItemRender<'a, T>)> = cite
        .items
        .drain(..)
        .map(|item| {
            let authorstring = item
                .rendered
                .find_names()
                .map(names_key)
                .unwrap_or_else(|| entry_author_key(item.entry));
            let authorstring =
                crate::csl::sort::normalize_name_sort_key_public(&authorstring);
            let citation_item = CitationItem::with_entry(item.entry);
            let group_key = style.group_sort_key(
                &citation_item,
                item.cite_props.speculative.citation_number,
                first_key,
                term_locale,
            );
            let (group_key, is_name_key) = group_key;
            (authorstring, group_key, is_name_key, item)
        })
        .collect();

    // First group by author string, preserving the normal-key order within a
    // group from the sort that already happened.
    entries.sort_by(|a, b| style.compare_sort_strings(&a.0, &b.0));

    // Replace each authorstring with the first normal key of its group plus
    // the item's position, so groups are ordered by that key.
    let mut start = 0;
    while start < entries.len() {
        let mut end = start + 1;
        while end < entries.len() && entries[end].0 == entries[start].0 {
            end += 1;
        }
        let base = if entries[start].2 {
            entries[start].1.split_whitespace().collect::<String>()
        } else {
            entries[start].1.clone()
        };
        for idx in start..end {
            entries[idx].0 = format!("{base}{idx}");
        }
        start = end;
    }
    entries.sort_by(|a, b| style.compare_sort_strings(&a.0, &b.0));

    cite.items = entries.into_iter().map(|(_, _, _, item)| item).collect();
}

fn collapse_items<'a, T: EntryLike>(cite: &mut SpeculativeCiteRender<'a, '_, T>) {
    let style = &cite.request.style;

    let after_collapse_delim = style
        .citation
        .after_collapse_delimiter
        .as_deref()
        .or(style.citation.layout.delimiter.as_deref());

    // citeproc-js applies its `after-collapse-delimiter` splice rules only
    // when the attribute is declared; without it the fallback above resolves
    // to the layout delimiter, which makes those rules no-ops.
    let has_after_collapse_delim = style.citation.after_collapse_delimiter.is_some();

    // CSL 1.0.2: `cite-group-delimiter` activates cite grouping when it is
    // declared; without it the layout delimiter joins cites (citeproc-js:
    // `collapse_YearSuffixCollapseNoYearSuffixDelimiter`,
    // `disambiguate_YearCollapseWithInstitution`).
    let group_delimiter = style.citation.cite_group_delimiter.as_deref().or(
        // For in-text collapses citeproc-js joins the cites of one author
        // group with a comma (its default `splice_delimiter`), not with the
        // citation layout delimiter.
        (style.settings.class == StyleClass::InText
            && matches!(
                style.citation.collapse,
                Some(Collapse::Year | Collapse::YearSuffix | Collapse::YearSuffixRanged)
            ))
        .then_some(", "),
    );
    let year_suffix_delimiter = style
        .citation
        .year_suffix_delimiter
        .as_deref()
        .or(style.citation.cite_group_delimiter.as_deref());

    match style.citation.collapse {
        Some(Collapse::CitationNumber) => {
            // Option with the start and end of the range.
            let mut range_start: Option<(usize, usize)> = None;
            let mut just_collapsed = false;

            let end_range = |items: &mut [SpeculativeItemRender<'a, T>],
                             range_start: &mut Option<(usize, usize)>,
                             just_collapsed: &mut bool| {
                let use_after_collapse_delim = *just_collapsed;
                *just_collapsed = false;

                if let &mut Some((start, end)) = range_start {
                    // If the previous citation range was collapsed, use the
                    // after-collapse delimiter before the next item.
                    if use_after_collapse_delim {
                        items[start].delim_override = after_collapse_delim;
                    }

                    // There should be at least three items in the range to
                    // collapse.
                    if start + 1 < end {
                        items[end].delim_override = Some("–");

                        for item in &mut items[start + 1..end] {
                            item.hidden = true;
                        }

                        *just_collapsed = true;
                    }
                }

                *range_start = None;
            };

            for i in 0..cite.items.len() {
                let citation_number = {
                    // Item must be borrowed in this block only because it
                    // cannot be mutably borrowed below otherwise.
                    let item = &cite.items[i];
                    // citeproc-js only collapses citation numbers for cites
                    // without locators: with a locator on every cite, a
                    // range would swallow the locators (`32–3, 32` instead of
                    // three separate cites).
                    if item.hidden
                        || item.locator.is_some()
                        || item.rendered.find_meta(&ElemMeta::CitationNumber).is_none()
                    {
                        end_range(&mut cite.items, &mut range_start, &mut just_collapsed);
                        continue;
                    }

                    item.cite_props.speculative.citation_number
                };

                let prev_citation_number = match range_start {
                    Some((_, end)) => {
                        Some(cite.items[end].cite_props.speculative.citation_number)
                    }
                    None => None,
                };

                match (range_start, prev_citation_number) {
                    (Some((start, end)), Some(prev_citation_number))
                        if end + 1 == i
                            && prev_citation_number + 1 == citation_number =>
                    {
                        // Extend the range.
                        range_start = Some((start, i));
                    }
                    _ => {
                        end_range(&mut cite.items, &mut range_start, &mut just_collapsed);
                        range_start = Some((i, i));
                    }
                }
            }

            end_range(&mut cite.items, &mut range_start, &mut just_collapsed);
        }
        Some(
            c @ (Collapse::Year | Collapse::YearSuffix | Collapse::YearSuffixRanged),
        ) => {
            // Index of where the current group started and the group we are
            // currently in.
            let mut group_idx: Option<(usize, usize)> = None;
            for i in 0..cite.items.len() {
                match group_idx {
                    // This is our group.
                    Some((_, idx)) if Some(idx) == cite.items[i].group_idx => {
                        // citeproc-js always splices with the
                        // after-collapse delimiter after a cite that carried
                        // a locator, even before a collapsed continuation.
                        let locator_after_collapse = has_after_collapse_delim
                            && i > 0
                            && cite.items[i - 1].locator.is_some();
                        if matches!(c, Collapse::YearSuffix | Collapse::YearSuffixRanged)
                            && let Some(s) =
                                cite.items[i].cite_props.speculative.year_suffix
                            && s > 0
                        {
                            // We want to collapse the years up to the suffix
                            // and the current item has a year suffix greater
                            // than zero, which means it follows another item
                            // with the same year. In this case, we collapse
                            // the year suffix.
                            cite.items[i].delim_override = if locator_after_collapse {
                                after_collapse_delim
                            } else {
                                year_suffix_delimiter
                            };
                            cite.items[i].collapse_verdict =
                                Some(CollapseVerdict::YearSuffix);
                            continue;
                        }
                        // FIXME: Retains delimiter in names.
                        cite.items[i].delim_override = if locator_after_collapse {
                            after_collapse_delim
                        } else {
                            group_delimiter
                        };
                        cite.items[i].collapse_verdict = Some(CollapseVerdict::First);
                    }
                    // This is a different group.
                    Some((start, _)) if start + 1 < i => {
                        cite.items[i].delim_override = after_collapse_delim;
                        group_idx = cite.items[i].group_idx.map(|idx| (i, idx));
                    }
                    // We are at the beginning, or the previous group held a
                    // single item: the current item is not a collapsed
                    // continuation, so the after-collapse delimiter follows —
                    // except under `collapse="year-suffix"`, where citeproc-js
                    // keeps the layout delimiter between two uncollapsed cites.
                    _ => {
                        if i > 0 && c != Collapse::YearSuffix {
                            cite.items[i].delim_override = after_collapse_delim;
                        }
                        group_idx = cite.items[i].group_idx.map(|idx| (i, idx));
                    }
                }
            }

            // For `year-suffix-ranged`, runs of three or more consecutive
            // year suffixes collapse into a range (`2000a–e`): the cites in
            // between are hidden and the range delimiter is placed before the
            // final cite of the run.
            if c == Collapse::YearSuffixRanged {
                fn year_suffix<T: EntryLike>(
                    item: &SpeculativeItemRender<'_, T>,
                ) -> Option<u32> {
                    item.cite_props.speculative.year_suffix.map(u32::from)
                }

                let mut group_start = 0;
                while group_start < cite.items.len() {
                    let Some(idx) = cite.items[group_start].group_idx else {
                        group_start += 1;
                        continue;
                    };
                    let mut group_end = group_start + 1;
                    while group_end < cite.items.len()
                        && cite.items[group_end].group_idx == Some(idx)
                    {
                        group_end += 1;
                    }

                    let mut start = group_start;
                    while start < group_end {
                        let Some(base) = year_suffix(&cite.items[start]) else {
                            start += 1;
                            continue;
                        };
                        let mut end = start;
                        while end + 1 < group_end
                            && year_suffix(&cite.items[end + 1])
                                == Some(base + (end + 1 - start) as u32)
                        {
                            end += 1;
                        }
                        if end > start + 1 {
                            for item in &mut cite.items[start + 1..end] {
                                item.hidden = true;
                            }
                            cite.items[end].delim_override = Some("–");
                        }
                        start = end + 1;
                    }

                    group_start = group_end;
                }
            }
        }
        None => {}
    }
}

fn substitute_subsequent_authors(
    subs: Option<&String>,
    mut rule: SubsequentAuthorSubstituteRule,
    items: &mut [(ElemChildren, String)],
) {
    if let Some(subs) = subs {
        let subs = Formatting::default().add_text(subs.clone());

        fn replace_all(names: &mut Elem, is_empty: bool, subs: &Formatted) {
            fn remove_name(mut child: Elem) -> Option<ElemChild> {
                if matches!(child.meta, Some(ElemMeta::Name(_, _))) {
                    return None;
                }
                child.children.0 = child
                    .children
                    .0
                    .into_iter()
                    .filter_map(|e| match e {
                        ElemChild::Elem(e) => remove_name(e),
                        _ => Some(e),
                    })
                    .collect();
                Some(ElemChild::Elem(child))
            }
            let old_children = std::mem::replace(
                &mut names.children,
                ElemChildren(vec![ElemChild::Text(subs.clone())]),
            );
            if !is_empty {
                for child in old_children.0 {
                    match child {
                        ElemChild::Elem(e) => {
                            if let Some(c) = remove_name(e) {
                                names.children.0.push(c);
                            }
                        }
                        // Name-joining text (` and `, `, `) disappears with
                        // the names; labels stay, which is why `Doe ed.`
                        // becomes `--- ed.`.
                        ElemChild::Text(text) => {
                            let trimmed =
                                text.text.trim().trim_matches([',', ';']).trim();
                            if !matches!(
                                trimmed,
                                "" | "and"
                                    | "&"
                                    | "et"
                                    | "y"
                                    | "und"
                                    | "et al."
                                    | "et al"
                                    | "and others"
                            ) {
                                names.children.0.push(ElemChild::Text(text));
                            }
                        }
                        other => names.children.0.push(other),
                    }
                }
            }
        }

        fn replace_name(e: Elem, subs: &Formatted) -> (ElemChild, bool) {
            if matches!(e.meta, Some(ElemMeta::Name(_, _))) {
                return (
                    ElemChild::Elem(Elem {
                        children: ElemChildren(vec![ElemChild::Text(subs.clone())]),
                        display: e.display,
                        meta: e.meta,
                        formatting: e.formatting,
                    }),
                    true,
                );
            }

            let len = e.children.0.len();
            let mut iter = e.children.0.into_iter();
            let mut children = Vec::with_capacity(len);
            let mut changed = false;
            for c in iter.by_ref() {
                match c {
                    ElemChild::Elem(ec) => {
                        let (nc, ch) = replace_name(ec, subs);
                        children.push(nc);
                        if ch {
                            changed = true;
                            break;
                        }
                    }
                    _ => children.push(c),
                }
            }
            children.extend(iter);
            (
                ElemChild::Elem(Elem {
                    display: e.display,
                    meta: e.meta,
                    children: ElemChildren(children),
                    formatting: e.formatting,
                }),
                changed,
            )
        }

        fn replace_each(names: &mut Elem, subs: &Formatted) {
            let old_children =
                std::mem::replace(&mut names.children, ElemChildren(Vec::new()));
            for child in old_children.0 {
                match child {
                    ElemChild::Elem(e) => {
                        names.children.0.push(replace_name(e, subs).0);
                    }
                    _ => names.children.0.push(child),
                }
            }
        }

        fn get_names(elem: &Elem, names: &mut Vec<Elem>) {
            if matches!(elem.meta, Some(ElemMeta::Name(_, _))) {
                names.push(elem.clone());
            } else {
                for c in &elem.children.0 {
                    if let ElemChild::Elem(e) = c {
                        get_names(e, names);
                    }
                }
            }
        }

        fn replace_first_n(mut num: usize, names: &mut Elem, subs: &Formatted) {
            let old_children =
                std::mem::replace(&mut names.children, ElemChildren(Vec::new()));
            for child in old_children.0.into_iter() {
                if num == 0 {
                    break;
                }
                match child {
                    ElemChild::Elem(e) => {
                        let (c, changed) = replace_name(e, subs);
                        names.children.0.push(c);
                        if changed {
                            num -= 1;
                        }
                    }
                    _ => names.children.0.push(child),
                }
            }
        }

        fn num_of_matches(ns1: &[String], ns2: &[String]) -> usize {
            ns1.iter().zip(ns2.iter()).take_while(|(a, b)| a == b).count()
        }

        let mut last_names = None;

        for item in items.iter_mut() {
            let ec = &mut item.0;
            let Some(names_elem) = ec.find_names() else {
                continue;
            };
            let mut xnames = Vec::new();
            get_names(names_elem, &mut xnames);
            // Compare the names themselves, not their roles or a label:
            // `editor` and `author` with the same person must match, and a
            // name label (`ed.`) is not part of the name.
            let xkeys: Vec<String> = xnames.iter().map(plain_elem).collect();
            let (lnames_elem, lnames) = if let Some(ns) = &last_names {
                ns
            } else {
                // No previous name; nothing to replace. Save and skip
                last_names = Some((names_elem.clone(), xkeys));
                continue;
            };
            if xnames.is_empty() {
                rule = SubsequentAuthorSubstituteRule::CompleteAll;
            }
            match rule {
                SubsequentAuthorSubstituteRule::CompleteAll => {
                    if lnames == &xkeys
                        && (!xnames.is_empty() || names_elem == lnames_elem)
                    {
                        let names = ec.find_names_mut().unwrap();
                        replace_all(names, xnames.is_empty(), &subs);
                    } else {
                        last_names = Some((names_elem.clone(), xkeys.clone()));
                    }
                }
                SubsequentAuthorSubstituteRule::CompleteEach => {
                    if lnames == &xkeys {
                        let names = ec.find_names_mut().unwrap();
                        replace_each(names, &subs);
                    } else {
                        last_names = Some((names_elem.clone(), xkeys.clone()));
                    }
                }
                SubsequentAuthorSubstituteRule::PartialEach => {
                    let nom = num_of_matches(&xkeys, lnames);
                    if nom > 0 {
                        let names = ec.find_names_mut().unwrap();
                        replace_first_n(nom, names, &subs);
                    } else {
                        last_names = Some((names_elem.clone(), xkeys.clone()));
                    }
                }
                SubsequentAuthorSubstituteRule::PartialFirst => {
                    let nom = num_of_matches(&xkeys, lnames);
                    if nom > 0 {
                        let names = ec.find_names_mut().unwrap();
                        replace_first_n(1, names, &subs);
                    } else {
                        last_names = Some((names_elem.clone(), xkeys.clone()));
                    }
                }
            }
        }
    }
}

/// What we have decided for rerendering this item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CollapseVerdict {
    /// Only the first date should be printed.
    First,
    /// Only the year suffix should be printed.
    YearSuffix,
}

/// The result of [`BibliographyDriver::finish`].
#[derive(Debug, Clone)]
pub struct Rendered {
    /// The bibliography items.
    pub bibliography: Option<RenderedBibliography>,
    /// The citation items.
    pub citations: Vec<RenderedCitation>,
}

/// A fully rendered bibliography.
#[derive(Debug, Clone)]
pub struct RenderedBibliography {
    /// Render the bibliography in a hanging indent.
    pub hanging_indent: bool,
    /// When set, the second field is aligned.
    pub second_field_align: Option<SecondFieldAlign>,
    /// The line spacing within the bibliography as a multiple of regular line
    /// spacing.
    pub line_spacing: NonZeroI16,
    /// Extra space between entries as a multiple of line height.
    pub entry_spacing: i16,
    /// The bibliography items. The first item may be some if
    /// `second_field_align` is set. Then, it is the first field that must be
    /// treated specially.
    pub items: Vec<BibliographyItem>,
}

/// A fully rendered bibliography item.
#[derive(Debug, Clone)]
pub struct BibliographyItem {
    /// The item's key as specified in the bibliography.
    pub key: String,
    /// The item's first field. Only available when required by the
    /// `second-field-align` CSL property.
    pub first_field: Option<ElemChild>,
    /// The formatting declared by the bibliography layout. Serializers that
    /// reproduce citeproc-js HTML apply it around the whole entry (including
    /// the second-field-align field divs), which is where citeproc-js opens
    /// the layout's formatting tags.
    pub formatting: Formatting,
    /// The rendered item.
    pub content: ElemChildren,
}

impl BibliographyItem {
    fn new(
        key: String,
        first_field: Option<ElemChild>,
        formatting: Formatting,
        content: ElemChildren,
    ) -> Self {
        Self { key, first_field, formatting, content }
    }
}

/// A fully rendered citation.
#[derive(Debug, Clone)]
pub struct RenderedCitation {
    /// The footnote number for this citation.
    pub note_number: Option<usize>,
    /// The citation.
    pub citation: ElemChildren,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sorting {
    Variable,
    Macro,
}

/// A context that contains all information related to rendering a single entry.
#[derive(Debug, Clone, PartialEq)]
struct InstanceContext<'a, T: EntryLike> {
    // Entry-dependent data.
    /// The current entry.
    pub entry: &'a T,
    /// The position of this citation in the list of citations.
    pub cite_props: CiteProperties<'a>,
    /// Whether we are sorting or formatting right now and if we are sorting with a variable or macro sort key.
    pub sorting: Option<Sorting>,
    /// The locale for the content in the entry.
    pub locale: Option<&'a LocaleCode>,
    /// The locale for the terms.
    pub term_locale: Option<&'a LocaleCode>,
    /// Whether this citation should respect a special form.
    pub kind: Option<SpecialForm>,
    /// Which labels were written.
    pub identifier_usage: RefCell<IdentifierUsage>,
}

impl<'a, T: EntryLike> InstanceContext<'a, T> {
    fn new(
        entry: &'a T,
        cite_props: CiteProperties<'a>,
        sorting: Option<Sorting>,
        locale: Option<&'a LocaleCode>,
        term_locale: Option<&'a LocaleCode>,
        kind: Option<SpecialForm>,
    ) -> Self {
        Self {
            entry,
            sorting,
            locale,
            term_locale,
            kind,
            identifier_usage: RefCell::new(cite_props.speculative.identifier_usage),
            cite_props,
        }
    }

    fn variable_sort_instance(item: &CitationItem<'a, T>, idx: usize) -> Self {
        Self::new(
            item.entry,
            CiteProperties::for_sorting(item.locator.clone(), idx),
            Some(Sorting::Variable),
            None,
            None,
            None,
        )
    }
}

/// A context that contains information about the style we are using to render.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StyleContext<'a> {
    // Settings from the style.
    /// The settings of the style.
    pub csl: &'a IndependentStyle,
    /// A list of locales defined in their respective locale file.
    locale_files: &'a [Locale],
    /// Which locale we're using.
    locale_override: Option<LocaleCode>,
    /// Document-wide name counts for given-name disambiguation rules other
    /// than `by-cite` (empty while sorting).
    pub(crate) name_registry: Option<&'a NameRegistry>,
}

impl<'a> StyleContext<'a> {
    fn new(
        style: &'a IndependentStyle,
        locale: Option<LocaleCode>,
        locale_files: &'a [Locale],
    ) -> Self {
        Self {
            csl: style,
            locale_files,
            locale_override: locale,
            name_registry: None,
        }
    }

    fn ctx<'b, T: EntryLike>(
        &'b self,
        entry: &'b T,
        cite_props: CiteProperties<'a>,
        locale: Option<&'b LocaleCode>,
        term_locale: Option<&'b LocaleCode>,
        bibliography: bool,
        cite_prefix: Option<&'b str>,
    ) -> Context<'b, T> {
        Context {
            instance: InstanceContext::new(
                entry,
                cite_props,
                None,
                locale,
                term_locale,
                None,
            ),
            style: self,
            writing: WritingContext::new(self.csl.settings.options.clone()),
            bibliography,
            cite_prefix,
            saw_names: false,
        }
    }

    fn macro_sorting_ctx<'b, T: EntryLike>(
        &'b self,
        item: &'b CitationItem<'b, T>,
        idx: usize,
        locale: Option<&'b LocaleCode>,
        term_locale: Option<&'b LocaleCode>,
        bibliography: bool,
    ) -> Context<'b, T> {
        Context {
            instance: InstanceContext::new(
                item.entry,
                CiteProperties::for_sorting(item.locator.clone(), idx),
                Some(Sorting::Macro),
                locale,
                term_locale,
                None,
            ),
            style: self,
            writing: WritingContext::new(self.csl.settings.options.clone()),
            bibliography,
            cite_prefix: None,
            saw_names: false,
        }
    }

    /// Render the given item within a citation.
    #[allow(clippy::too_many_arguments)]
    fn citation<T: EntryLike>(
        &self,
        entry: &T,
        props: CiteProperties<'a>,
        locale: Option<&LocaleCode>,
        term_locale: Option<&LocaleCode>,
        kind: Option<CitePurpose>,
        collapse_verdict: Option<CollapseVerdict>,
        cite_prefix: Option<&str>,
    ) -> ElemChildren {
        let ctx = self.do_citation(
            entry,
            props,
            locale,
            term_locale,
            kind,
            collapse_verdict,
            cite_prefix,
        );
        ctx.flush()
    }

    /// Render the given item within a bibliography.
    fn bibliography<T: EntryLike>(
        &self,
        entry: &T,
        props: CiteProperties<'a>,
        locale: Option<&LocaleCode>,
        term_locale: Option<&LocaleCode>,
    ) -> Option<ElemChildren> {
        self.do_bibliography(entry, props, locale, term_locale)
            .map(|ctx| ctx.flush())
    }

    /// Render the given item within a citation.
    #[allow(clippy::too_many_arguments)]
    fn do_citation<'b, T: EntryLike>(
        &'b self,
        entry: &'b T,
        props: CiteProperties<'a>,
        locale: Option<&'b LocaleCode>,
        term_locale: Option<&'b LocaleCode>,
        kind: Option<CitePurpose>,
        collapse_verdict: Option<CollapseVerdict>,
        cite_prefix: Option<&'b str>,
    ) -> Context<'b, T> {
        let mut ctx = self.ctx(entry, props, locale, term_locale, false, cite_prefix);

        let do_regular = |ctx: &mut Context<'b, T>| {
            let reset = if ctx.instance.kind.is_none() {
                match collapse_verdict {
                    Some(CollapseVerdict::First) => {
                        ctx.set_special_form(Some(SpecialForm::OnlyFirstDate));
                        true
                    }
                    Some(CollapseVerdict::YearSuffix) => {
                        ctx.set_special_form(Some(SpecialForm::OnlyYearSuffix));
                        true
                    }
                    None => false,
                }
            } else {
                false
            };

            ctx.writing.push_name_options(&self.csl.citation.name_options);
            self.csl.citation.layout.render(ctx);
            ctx.writing.pop_name_options();

            if reset {
                ctx.set_special_form(None);
            }
        };

        let do_author = |ctx: &mut Context<'b, T>| {
            let author_var = Variable::Name(
                if entry.resolve_name_variable(NameVariable::Author).is_empty()
                    && !entry.resolve_name_variable(NameVariable::Editor).is_empty()
                {
                    NameVariable::Editor
                } else {
                    NameVariable::Author
                },
            );

            if self.csl.citation.layout.will_render(ctx, author_var) {
                // Render name from citation.
                ctx.set_special_form(Some(SpecialForm::VarOnly(author_var)));
                do_regular(ctx);
            } else {
                let mut needs_bibliography = true;

                // Render name from citation with ibid forced to Different.
                if ctx.instance.cite_props.speculative.ibid != IbidState::Different {
                    let prev_ibid = ctx.instance.cite_props.speculative.ibid;
                    ctx.instance.cite_props.speculative.ibid = IbidState::Different;
                    if self.csl.citation.layout.will_render(ctx, author_var) {
                        ctx.set_special_form(Some(SpecialForm::VarOnly(author_var)));
                        do_regular(ctx);
                        needs_bibliography = false;
                    }
                    ctx.instance.cite_props.speculative.ibid = prev_ibid;
                }

                if needs_bibliography {
                    // Render name from bibliography.
                    ctx.set_special_form(Some(SpecialForm::VarOnly(author_var)));
                    let needs_synthesis =
                        if let Some(bibliography) = &self.csl.bibliography {
                            if bibliography.layout.will_render(ctx, author_var) {
                                ctx.writing.push_name_options(&bibliography.name_options);
                                bibliography.layout.render(ctx);
                                ctx.writing.pop_name_options();
                                false
                            } else {
                                true
                            }
                        } else {
                            true
                        };

                    if needs_synthesis {
                        // We build our own name and render it with the citation's
                        // properties.
                        let layout = Layout::new(
                            vec![LayoutRenderingElement::Names(Names::with_variables(
                                vec![NameVariable::Author],
                            ))],
                            self.csl.citation.layout.to_formatting(),
                            None,
                            None,
                        );
                        ctx.writing.push_name_options(&self.csl.citation.name_options);
                        layout.render(ctx);
                        ctx.writing.pop_name_options();
                    }
                }
            }
            ctx.set_special_form(None);
        };

        match (kind, self.csl.bibliography.as_ref()) {
            (Some(CitePurpose::Author), _) => {
                do_author(&mut ctx);
            }
            (Some(CitePurpose::Full), Some(bib)) => {
                ctx.writing.push_name_options(&bib.name_options);
                bib.layout.render(&mut ctx);
                ctx.writing.pop_name_options();

                if bib.second_field_align.is_some()
                    && let Some(mut t) =
                        ctx.writing.elem_stack.first_mut().remove_any_meta()
                {
                    if let ElemChild::Text(t) = &mut t {
                        t.text.push(' ');
                    } else if let ElemChild::Elem(e) = &mut t
                        && let Some(t) = e.children.last_text_mut()
                    {
                        t.text.push(' ');
                    }

                    ctx.writing.elem_stack.first_mut().0.insert(0, t);
                }
            }
            (Some(CitePurpose::Prose), _) => {
                let ambient = *ctx.writing.formatting();
                let author_loc = ctx.apply_prefix(&Affixes::default(), ambient);
                do_author(&mut ctx);
                let has_author = ctx.writing.has_content_since(&author_loc);
                ctx.apply_suffix(&Affixes::default(), author_loc, ambient);

                if self.csl.info.category.iter().any(|c| {
                    matches!(
                        c,
                        StyleCategory::CitationFormat {
                            format: CitationFormat::Label | CitationFormat::Numeric
                        }
                    )
                }) {
                    if has_author
                        && !self.csl.citation.layout.prefix.as_ref().is_some_and(|f| {
                            f.chars().next().is_some_and(char::is_whitespace)
                        })
                    {
                        ctx.ensure_space();
                    }

                    // Print the label.
                    if let Some(prefix) = self.csl.citation.layout.prefix.as_ref() {
                        ctx.push_str(prefix);
                    }
                    do_regular(&mut ctx);
                    if let Some(suffix) = self.csl.citation.layout.suffix.as_ref() {
                        ctx.push_str(suffix);
                    }
                } else {
                    // Print the citation surrounded by parentheses and suppress
                    // the author.
                    let mut prefix = self
                        .csl
                        .citation
                        .layout
                        .prefix
                        .clone()
                        .unwrap_or_else(|| "(".to_string());
                    if has_author
                        && !prefix.chars().next().is_some_and(char::is_whitespace)
                    {
                        prefix.insert(0, ' ');
                    }
                    let affixes = Affixes {
                        prefix: Some(prefix),
                        suffix: Some(
                            self.csl
                                .citation
                                .layout
                                .suffix
                                .clone()
                                .unwrap_or_else(|| ")".to_string()),
                        ),
                    };
                    let ambient = *ctx.writing.formatting();
                    let affix_loc = ctx.apply_prefix(&affixes, ambient);
                    ctx.set_special_form(Some(SpecialForm::SuppressAuthor));
                    do_regular(&mut ctx);
                    ctx.set_special_form(None);
                    if has_author {
                        ctx.apply_suffix(&affixes, affix_loc, ambient);
                    } else {
                        ctx.push_str(affixes.suffix.as_deref().unwrap());
                        ctx.commit_elem(affix_loc.0, None, None);
                    }
                }
            }
            (Some(CitePurpose::SuppressAuthor), _) => {
                ctx.set_special_form(Some(SpecialForm::SuppressAuthor));
                do_regular(&mut ctx);
                ctx.set_special_form(None);
            }
            (Some(CitePurpose::Year) | Some(CitePurpose::Full) | None, _) => {
                do_regular(&mut ctx);
            }
        }
        ctx
    }

    /// Render the given item within a bibliography.
    fn do_bibliography<'b, T: EntryLike>(
        &'b self,
        entry: &'b T,
        props: CiteProperties<'a>,
        locale: Option<&'b LocaleCode>,
        term_locale: Option<&'b LocaleCode>,
    ) -> Option<Context<'b, T>> {
        let mut ctx = self.ctx(entry, props, locale, term_locale, true, None);
        ctx.writing
            .push_name_options(&self.csl.bibliography.as_ref()?.name_options);

        let layout = &self.csl.bibliography.as_ref()?.layout;
        let affixes = layout.to_affixes();

        let ambient = *ctx.writing.formatting();
        let affix_loc = ctx.apply_prefix(&affixes, ambient);
        layout.render(&mut ctx);
        ctx.apply_bibliography_suffix(&affixes, affix_loc, ambient);

        Some(ctx)
    }

    /// Return the locale to use for this style.
    fn locale(&self) -> LocaleCode {
        self.locale_override
            .clone()
            .or_else(|| self.csl.default_locale.clone())
            .unwrap_or_else(LocaleCode::en_us)
    }
}

/// A citation request. A citation can contain references to multiple items.
#[derive(Debug, PartialEq)]
pub struct CitationRequest<'a, T: EntryLike> {
    /// The items to format.
    pub items: Vec<CitationItem<'a, T>>,
    /// Which style to use for the citation.
    style: &'a IndependentStyle,
    /// The requested locale for the style's terms.
    ///
    /// This is also the place to store a locale override from a dependent
    /// style.
    pub locale: Option<LocaleCode>,
    /// The files used to retrieve locale settings and terms if the style does
    /// not define all necessary items.
    pub locale_files: &'a [Locale],
    /// The number to use for `first-reference-note-number`.
    ///
    /// `near-note` will always test false if this is none for the referenced
    /// note.
    note_number: Option<usize>,
}

impl<'a, T: EntryLike> CitationRequest<'a, T> {
    /// Create a new citation request.
    pub fn new(
        items: Vec<CitationItem<'a, T>>,
        style: &'a IndependentStyle,
        locale: Option<LocaleCode>,
        locale_files: &'a [Locale],
        note_number: Option<usize>,
    ) -> Self {
        Self {
            items,
            style,
            locale,
            locale_files,
            note_number: note_number.filter(|_| style.settings.class == StyleClass::Note),
        }
    }

    /// Create a new citation request without a note number.
    pub fn from_items(
        items: Vec<CitationItem<'a, T>>,
        style: &'a IndependentStyle,
        locale_files: &'a [Locale],
    ) -> Self {
        Self::new(items, style, None, locale_files, None)
    }

    fn style(&self) -> StyleContext<'a> {
        StyleContext::new(self.style, self.locale.clone(), self.locale_files)
    }

    /// Whether the request's layout affixes (citation prefix/suffix) apply.
    /// Suppressed-author citations keep the layout affixes (citeproc-js
    /// renders `suppress-author` as `(2006)` for author-date styles); the
    /// purposes that carry their own affixes (prose, author-only, year, full)
    /// do not.
    fn shall_affix(&self) -> bool {
        self.items
            .iter()
            .all(|p| matches!(p.purpose, None | Some(CitePurpose::SuppressAuthor)))
    }

    fn prefix(&self) -> Option<&'a str> {
        self.style
            .citation
            .layout
            .prefix
            .as_deref()
            .filter(|_| self.shall_affix())
    }

    fn suffix(&self) -> Option<&'a str> {
        self.style
            .citation
            .layout
            .suffix
            .as_deref()
            .filter(|_| self.shall_affix())
    }
}

/// A request to render a bibliography. Use with [`BibliographyDriver::finish`].
#[derive(Debug, PartialEq)]
pub struct BibliographyRequest<'a> {
    /// Which style to use for the bibliography. Some styles do not have a
    /// bibliography, in which case the field of the [`Rendered`] will be
    /// `None`.
    pub style: &'a IndependentStyle,
    /// The requested locale for the style's terms.
    ///
    /// This is also the place to store a locale override from a dependent
    /// style.
    pub locale: Option<LocaleCode>,
    /// The files used to retrieve locale settings and terms if the style does
    /// not define all necessary items.
    pub locale_files: &'a [Locale],
}

impl<'a> BibliographyRequest<'a> {
    /// Create a new bibliography request.
    pub fn new(
        style: &'a IndependentStyle,
        locale: Option<LocaleCode>,
        locale_files: &'a [Locale],
    ) -> Self {
        Self { style, locale, locale_files }
    }

    fn style(&self) -> StyleContext<'a> {
        StyleContext::new(self.style, self.locale.clone(), self.locale_files)
    }
}

/// The position of a citation relative to earlier citations of the same
/// entry.
///
/// Processors derive this from citation order and note numbers. Setting it
/// on a [`CitationItem`] overrides the derived state, e.g. when replaying a
/// document whose position state is managed externally.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CitePosition {
    /// The first citation of the entry.
    First,
    /// The entry was cited before.
    Subsequent,
    /// Directly following a citation of the same entry with the same locator.
    Ibid,
    /// Directly following a citation of the same entry with a different
    /// locator.
    IbidWithLocator,
}

impl CitePosition {
    /// Whether this position satisfies the given CSL position test.
    ///
    /// Like citeproc-js, the tests are ranked: `ibid-with-locator` also
    /// satisfies `ibid`, and both also satisfy `subsequent`.
    pub(crate) fn matches(self, test: citationberg::TestPosition) -> bool {
        use citationberg::TestPosition;

        match test {
            TestPosition::First => self == Self::First,
            TestPosition::Subsequent => self != Self::First,
            TestPosition::Ibid => matches!(self, Self::Ibid | Self::IbidWithLocator),
            TestPosition::IbidWithLocator => self == Self::IbidWithLocator,
            // `near-note` also depends on the near-note flag and is handled
            // by the renderer.
            TestPosition::NearNote => false,
        }
    }
}

/// A reference to an [`crate::Entry`] within a [`CitationRequest`].
#[derive(Debug, Clone, PartialEq)]
pub struct CitationItem<'a, T: EntryLike> {
    /// The entry to format.
    pub entry: &'a T,
    /// The locator that specifies where in the entry the item is found.
    pub locator: Option<SpecificLocator<'a>>,
    /// A locale code that overrides the assumed locale of the entry. If this is
    /// none, this will default to [`CitationRequest::locale`] and then
    /// [`citationberg::IndependentStyle::default_locale`].
    pub locale: Option<LocaleCode>,
    /// Whether this item will be included in the output.
    pub hidden: bool,
    /// Format the item in a special way.
    pub purpose: Option<CitePurpose>,
    /// Literal text placed directly before the item's rendered content.
    ///
    /// The prefix is inserted inside the citation layout's inter-item
    /// delimiters. It is not processed with locale or quote handling.
    pub prefix: Option<String>,
    /// Literal text placed directly after the item's rendered content.
    ///
    /// The suffix is inserted inside the citation layout's inter-item
    /// delimiters. It is not processed with locale or quote handling.
    pub suffix: Option<String>,
    /// Overrides the citation position derived from citation order.
    pub position: Option<CitePosition>,
    /// Overrides whether this citation is within `near-note-distance` of the
    /// previous citation of the same entry.
    ///
    /// Like citeproc-js, `near-note` only tests true when the position is not
    /// `first`.
    pub near_note: Option<bool>,
    /// The initial index of this item in the list of items.
    initial_idx: usize,
}

impl<'a, T: EntryLike> CitationItem<'a, T> {
    /// Create a new citation item for the given entry.
    pub fn with_entry(entry: &'a T) -> Self {
        Self {
            entry,
            locator: None,
            locale: None,
            hidden: false,
            purpose: None,
            prefix: None,
            suffix: None,
            position: None,
            near_note: None,
            initial_idx: 0,
        }
    }

    /// Create a new citation item with a locator for the given entry.
    pub fn with_locator(entry: &'a T, locator: Option<SpecificLocator<'a>>) -> Self {
        Self {
            entry,
            locator,
            locale: None,
            hidden: false,
            purpose: None,
            prefix: None,
            suffix: None,
            position: None,
            near_note: None,
            initial_idx: 0,
        }
    }

    /// Create a new citation with all fields set.
    pub fn new(
        entry: &'a T,
        locator: Option<SpecificLocator<'a>>,
        locale: Option<LocaleCode>,
        hidden: bool,
        purpose: Option<CitePurpose>,
    ) -> Self {
        Self {
            entry,
            locator,
            locale,
            hidden,
            purpose,
            prefix: None,
            suffix: None,
            position: None,
            near_note: None,
            initial_idx: 0,
        }
    }

    /// Change the `kind` of this item.
    pub fn kind(mut self, purpose: CitePurpose) -> Self {
        self.purpose = Some(purpose);
        self
    }

    /// Set literal affixes that are placed directly before and after this
    /// item's rendered content, inside the citation layout's inter-item
    /// delimiters.
    pub fn with_affixes(
        mut self,
        prefix: Option<String>,
        suffix: Option<String>,
    ) -> Self {
        self.prefix = prefix;
        self.suffix = suffix;
        self
    }

    /// Force the citation position of this item instead of deriving it from
    /// citation order.
    pub fn with_position(mut self, position: CitePosition) -> Self {
        self.position = Some(position);
        self
    }

    /// Force whether this item counts as a near note, instead of deriving it
    /// from the previous citation's note number.
    pub fn with_near_note(mut self, near_note: bool) -> Self {
        self.near_note = Some(near_note);
        self
    }
}

impl<'a> StyleContext<'a> {
    /// Retrieve a macro.
    fn get_macro(&self, name: &str) -> Option<&'a CslMacro> {
        self.csl.macros.iter().find(|m| m.name == name)
    }

    /// Get the locale for the given language in the style.
    fn lookup_locale<F, R>(&self, mut f: F) -> Option<R>
    where
        F: FnMut(&'a Locale) -> Option<R>,
    {
        let mut lookup = |file: &'a [Locale], lang: Option<&LocaleCode>| {
            #[allow(clippy::redundant_closure)]
            file.iter().find(|l| l.lang.as_ref() == lang).and_then(|l| f(l))
        };

        let locale = self.locale();
        let en_us = LocaleCode::en_us();

        for (i, resource) in [self.csl.locale.as_slice(), self.locale_files]
            .into_iter()
            .enumerate()
        {
            let fallback = if i == 0 {
                locale.parse_base().and_then(|base| match base {
                    BaseLanguage::Iso639_1(lang) => {
                        Some(LocaleCode(String::from_utf8(lang.to_vec()).ok()?))
                    }
                    BaseLanguage::Iana(lang) => Some(LocaleCode(lang)),
                    _ => None,
                })
            } else {
                locale.fallback()
            };

            if let Some(output) = lookup(resource, Some(&locale)) {
                return Some(output);
            }

            if fallback.is_some()
                && let Some(output) = lookup(resource, fallback.as_ref())
            {
                return Some(output);
            }

            if i == 0 {
                if let Some(output) = lookup(resource, None) {
                    return Some(output);
                }
            } else if let Some(output) = lookup(resource, Some(&en_us)) {
                return Some(output);
            }
        }

        None
    }

    /// Check whether to do punctuation in quotes.
    fn punctuation_in_quotes(&self) -> bool {
        self.lookup_locale(|f| f.style_options?.punctuation_in_quote)
            .unwrap_or_default()
    }
}

/// This struct contains all information needed to render a single entry. It
/// contains buffers and is mutable.
#[derive(Debug, Clone)]
pub(crate) struct WritingContext {
    // Dynamic settings that change while rendering.
    /// Whether to watch out for punctuation that should be pulled inside the
    /// preceding quoted content.
    pull_punctuation: bool,
    /// The current state of the smart quote conversion.
    quoter: SmartQuoter,
    /// Whether to strip periods.
    strip_periods: bool,
    /// Whether to add queried variables to the suppression list.
    suppress_queried_variables: bool,
    /// Suppressed variables that must not be rendered.
    suppressed_variables: RefCell<Vec<Variable>>,
    /// Whether this render has checked for `disambiguate` in `cs:choose`.
    checked_disambiguate: bool,
    /// How many `disambiguate="true"` conditions were active in this render.
    disambiguate_count: u8,
    /// Check whether this is the first date.
    first_date: bool,
    /// The disambiguation-relevant properties of the first `cs:name` element.
    /// This is `None` if no `cs:name` elements were rendered.
    first_name: Option<NameDisambiguationProperties>,

    // Inheritable settings.
    /// A stack of formatting. Always contains the format of the root layout
    /// element at the bottom. Each element with a formatting may push and, if
    /// it did push, must remove. Its formatting shall apply for it and its
    /// children.
    format_stack: NonEmptyStack<Formatting>,
    /// Text cases.
    cases: NonEmptyStack<Option<Case>>,
    /// Inheritable name options.
    name_options: NonEmptyStack<InheritableNameOptions>,
    /// Delimiters from ancestor delimiting elements (e.g., `cs:group`).
    /// To be applied within `cs:choose`, but not another delimiting element or a macro.
    delimiters: NonEmptyStack<Option<String>>,

    // Buffers.
    /// The buffer we're writing to. If block-level or formatting changes, we
    /// flush the buffer to the last [`Elem`] in the elem stack.
    buf: CaseFolder,
    /// A list of in-progress subtrees. Elements that are to be nested are
    /// pushed and then either popped or inserted at the end of their ancestor.
    elem_stack: NonEmptyStack<ElemChildren>,
}

impl Default for WritingContext {
    fn default() -> Self {
        Self {
            pull_punctuation: false,
            quoter: SmartQuoter::default(),
            strip_periods: false,
            suppress_queried_variables: false,
            suppressed_variables: RefCell::new(Vec::new()),
            checked_disambiguate: false,
            disambiguate_count: 0,
            first_date: true,
            first_name: None,
            format_stack: NonEmptyStack::default(),
            cases: NonEmptyStack::default(),
            name_options: NonEmptyStack::default(),
            delimiters: NonEmptyStack::default(),
            buf: CaseFolder::default(),
            elem_stack: NonEmptyStack::default(),
        }
    }
}

impl WritingContext {
    fn new(options: InheritableNameOptions) -> Self {
        Self {
            name_options: NonEmptyStack::new(options),
            ..Self::default()
        }
    }

    /// Retrieve the current formatting.
    fn formatting(&self) -> &Formatting {
        self.format_stack.last()
    }

    /// Push a format on top of the stack if it is not empty.
    fn push_format(&mut self, format: citationberg::Formatting) -> FormatIdx {
        if format.is_empty() {
            return FormatIdx(self.format_stack.len());
        }

        self.save_to_block();
        let pos = self.format_stack.len();
        self.format_stack.push(self.formatting().apply(format));
        FormatIdx(pos)
    }

    /// Pop a format from the stack if it is not empty.
    fn pop_format(&mut self, pos: FormatIdx) {
        if pos.0 == self.format_stack.len() {
            return;
        }

        self.save_to_block();
        self.format_stack.drain(pos.0).for_each(drop);
    }

    /// Saves the current buffer to the last element in the finished list. This
    /// must happen if [`Display`] or formatting changes, as well as when we're
    /// done with an element.
    fn save_to_block(&mut self) {
        if self.buf.is_empty() {
            return;
        }

        let format = *self.formatting();

        // Append to last child if formats match.
        if let Some(child) = self.elem_stack.last_mut().0.last_mut()
            && let ElemChild::Text(child) = child
            && format == child.formatting
        {
            child.text.push_str(&mem::take(&mut self.buf).finish());
            return;
        }

        let formatted = format.add_text(mem::take(&mut self.buf).finish());
        self.elem_stack.last_mut().0.push(ElemChild::Text(formatted))
    }

    /// Add another subtree to the children element. This must be done to
    /// include a new element or to check that the subtree is empty.
    fn push_elem(&mut self, format: citationberg::Formatting) -> DisplayLoc {
        self.save_to_block();
        let pos = self.elem_stack.len();
        self.elem_stack.push(ElemChildren::new());
        DisplayLoc::new(pos, self.push_format(format), Formatting::default())
    }

    /// Remove the last subtree and discard it.
    ///
    /// Will panic if the location does not match.
    fn discard_elem(&mut self, loc: DisplayLoc) {
        if self.elem_stack.len().get() != loc.0.get() + 1 {
            panic!("stack location does not match");
        }
        assert_eq!(
            self.elem_stack.len().get(),
            loc.0.get() + 1,
            "stack location does not match"
        );
        self.pop_format(loc.1);

        self.save_to_block();
        self.elem_stack.drain(loc.0).for_each(drop);
    }

    fn has_content_since(&mut self, loc: &(DisplayLoc, usize)) -> bool {
        self.save_to_block();
        let children = self.elem_stack.last();
        let has_content = match children.0.first() {
            Some(ElemChild::Text(t)) if loc.1 < t.text.len() => {
                t.text[loc.1..].chars().any(|c| !c.is_whitespace())
            }
            Some(ElemChild::Text(_)) => false,
            Some(ElemChild::Elem(e)) => e.has_content(),
            Some(
                ElemChild::Markup(_)
                | ElemChild::Link { .. }
                | ElemChild::Transparent { .. },
            ) => true,
            None => false,
        };

        has_content || children.0.iter().skip(1).any(ElemChild::has_content)
    }

    /// Apply a prefix, but return a tuple that allows us to undo it if it
    /// wasn't followed by anything.
    ///
    /// `ambient` is the formatting that was in effect before the element's
    /// own formatting was applied. Affixes are decorated by their element's
    /// ancestors but not by the element itself (citeproc-js appends
    /// prefix/suffix after the element's own decorations), so when the
    /// element re-declares formatting, the prefix is written as its own run
    /// under `ambient`.
    fn apply_prefix(
        &mut self,
        affixes: &Affixes,
        ambient: Formatting,
    ) -> (DisplayLoc, usize) {
        let pos = self.push_elem(citationberg::Formatting::default());
        if let Some(prefix) = &affixes.prefix {
            self.push_affix_text(prefix, ambient);
        };

        (pos, affixes.prefix.as_ref().map(|p| p.len()).unwrap_or_default())
    }

    /// Add `text` to the buffer as an affix.
    ///
    /// If the element re-declared formatting, the buffered content is flushed
    /// first and the affix is written as its own run under `ambient`, the
    /// element's ancestor formatting. Otherwise the affix simply joins the
    /// surrounding run.
    fn push_affix_text(&mut self, text: &str, ambient: Formatting) {
        if ambient == *self.formatting() {
            self.buf.push_str(text);
            return;
        }

        self.save_to_block();
        let prev = mem::replace(self.format_stack.last_mut(), ambient);
        self.buf.push_str(text);
        self.save_to_block();
        *self.format_stack.last_mut() = prev;
    }

    /// Nest the last subtree into its ancestor like [`Self::commit_elem`],
    /// but prepend `delimiter` (in the enclosing formatting) when the subtree
    /// rendered any content. Returns whether it did.
    ///
    /// This mirrors the CSL spec: a delimiter "delimits non-empty pieces of
    /// output", so a piece that renders nothing must not leave its delimiter
    /// behind.
    fn commit_elem_with_delimiter(
        &mut self,
        loc: DisplayLoc,
        delimiter: Option<&str>,
    ) -> bool {
        assert_eq!(
            self.elem_stack.len().get(),
            loc.0.get() + 1,
            "stack location does not match"
        );
        self.pop_format(loc.1);

        self.save_to_block();
        let mut children = self.elem_stack.pop().unwrap();
        let has_content = children.has_content();

        if has_content && let Some(delimiter) = delimiter {
            let formatting = *self.formatting();
            children
                .0
                .insert(0, ElemChild::Text(formatting.add_text(delimiter.to_string())));
        }

        self.elem_stack.last_mut().0.extend(children.0);
        has_content
    }

    /// Nest the last subtree into its ancestor. If the `display` argument is
    /// some, a new element child will be created there. Otherwise, we will
    /// append the children of the last subtree to the children of its ancestor.
    fn commit_elem(
        &mut self,
        loc: DisplayLoc,
        display: Option<Display>,
        meta: Option<ElemMeta>,
    ) {
        assert_eq!(
            self.elem_stack.len().get(),
            loc.0.get() + 1,
            "stack location does not match"
        );
        self.pop_format(loc.1);

        self.save_to_block();
        let children = self.elem_stack.pop().unwrap();

        if display.is_some()
            || meta.is_some()
            || (loc.2 != Formatting::default() && children.has_content())
        {
            self.elem_stack
                .last_mut()
                .0
                .push(Elem { children, display, meta, formatting: loc.2 }.into());
        } else {
            self.elem_stack.last_mut().0.extend(children.0);
        }
    }

    /// Push an item on the name options stack.
    pub fn push_name_options(&mut self, options: &InheritableNameOptions) {
        self.name_options.push(self.name_options.last().apply(options));
    }

    /// Pop an item from the name options stack.
    pub fn pop_name_options(&mut self) {
        self.name_options.pop();
    }

    /// Ensure that the buffer is either empty or the last character is a space.
    pub fn ensure_space(&mut self) {
        if !self.buf.is_empty() {
            if !self.buf.ends_with(' ') && !self.buf.ends_with('\u{a0}') {
                self.buf.push(' ');
            }
        } else if let Some(l) = self.elem_stack.last_mut().last_text_mut()
            && !l.text.ends_with(' ')
            && !l.text.ends_with('\u{a0}')
        {
            l.text.push(' ');
        }
    }

    /// Folds all remaining elements into the first element and returns it.
    fn flush(mut self) -> ElemChildren {
        self.save_to_block();

        assert_eq!(
            self.format_stack.len().get(),
            1,
            "formatting stack is not one but {}",
            self.format_stack.len()
        );

        self.elem_stack.finish()
    }

    /// Set whether to strip periods.
    fn may_strip_periods(&mut self, strip: bool) {
        self.strip_periods = strip;
    }

    /// Stop stripping periods.
    fn stop_stripping_periods(&mut self) {
        self.strip_periods = false;
    }

    /// Start suppressing the queried variables.
    fn start_suppressing_queried_variables(&mut self) {
        self.suppress_queried_variables = true;
    }

    /// Stop suppressing the queried variables.
    fn stop_suppressing_queried_variables(&mut self) {
        self.suppress_queried_variables = false;
    }

    /// Set the case of the next text.
    fn push_case(&mut self, case: Option<Case>) -> CaseIdx {
        let idx = self.cases.len();
        self.cases.push(case);
        CaseIdx(idx)
    }

    /// Clear the case of the next text.
    fn pop_case(&mut self, idx: CaseIdx) {
        if idx.0 == self.cases.len() {
            return;
        }

        self.cases.drain(idx.0).for_each(drop);
    }
    /// Reconfigures the case folder's case to the current
    fn reconfigure(&mut self) {
        self.buf.reconfigure((*self.cases.last()).unwrap_or_default());
    }

    /// Set the delimiter of the children of a [`citationberg::Group`] or
    /// [`citationberg::Layout`]. It is inherited by [`citationberg::Choose`]
    /// for its children as well.
    fn push_delimiter(&mut self, delimiter: Option<String>) -> DelimiterIdx {
        let idx = self.delimiters.len();
        self.delimiters.push(delimiter);
        DelimiterIdx(idx)
    }
    /// Clear the delimiter after a [`citationberg::Group`] or
    /// [`citationberg::Layout`].
    fn pop_delimiter(&mut self, idx: DelimiterIdx) {
        if idx.0 == self.delimiters.len() {
            return;
        }

        self.delimiters.drain(idx.0).for_each(drop);
    }

    /// Push a new suppressed variable if we are suppressing queried variables.
    /// The string in which the last rendered output lives: the raw buffer if
    /// it has content, otherwise the deepest trailing text of the element
    /// stack (rich-text runs commit their text into nested elements).
    fn last_mut_text(&mut self) -> Option<&mut String> {
        if !self.buf.is_empty() {
            return Some(self.buf.as_string_mut());
        }
        self.elem_stack
            .last_mut_predicate(|p| !p.is_empty())
            .and_then(|p| p.last_text_mut())
            .map(|f| &mut f.text)
    }

    fn maybe_suppress(&self, variable: Variable) {
        if self.suppress_queried_variables {
            self.suppressed_variables.borrow_mut().push(variable);
        }
    }

    fn prepare_variable_query<V>(&self, variable: V) -> Option<Variable>
    where
        V: Into<Variable>,
    {
        let general: Variable = variable.into();
        if self.suppressed_variables.borrow().contains(&general) {
            return None;
        }

        self.maybe_suppress(general);
        Some(general)
    }

    /// Return the sum of the lengths of strings in the finished elements. This
    /// may not monotonically increase.
    fn len(&self) -> usize {
        self.buf.len()
            + self
                .elem_stack
                .iter()
                .flat_map(|e| e.0.iter().map(ElemChild::str_len))
                .sum::<usize>()
    }

    /// Write the [`NameDisambiguationProperties`] that the first `cs:name`
    /// element used. Do not change if this is not the first `cs:name` element.
    /// Returns whether this was the first `cs:name` element.
    fn first_name_properties<F>(&mut self, f: F) -> bool
    where
        F: FnOnce() -> NameDisambiguationProperties,
    {
        if self.first_name.is_none() {
            self.first_name = Some(f());
            true
        } else {
            false
        }
    }
}

pub(crate) struct Context<'a, T: EntryLike> {
    instance: InstanceContext<'a, T>,
    style: &'a StyleContext<'a>,
    writing: WritingContext,
    bibliography: bool,
    /// The literal prefix of the citation item being rendered, if any. Used
    /// to decide whether a leading term starts a new sentence.
    cite_prefix: Option<&'a str>,
    /// Whether a `cs:names` element rendered in this context. Sort-key
    /// rendering uses it to build structured name keys.
    pub(crate) saw_names: bool,
}

#[derive(Debug, Clone, PartialEq)]
struct CiteProperties<'a> {
    pub certain: CertainCiteProperties,
    pub speculative: SpeculativeCiteProperties<'a>,
}

impl<'a> CiteProperties<'a> {
    fn for_sorting(locator: Option<SpecificLocator<'a>>, citation_number: usize) -> Self {
        Self {
            certain: CertainCiteProperties::new(),
            speculative: SpeculativeCiteProperties::speculate(
                locator,
                citation_number,
                IbidState::Different,
            ),
        }
    }
}

/// Item properties that can be determined before the first render of a
/// citation or bibliography entry.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
struct CertainCiteProperties {
    /// The number of the footnote this citation appears in.
    ///
    /// We can determine this because it depends on citation order only. May be
    /// none if the current style is in-text.
    pub note_number: Option<usize>,
    /// The number of the first footnote this citation appears in.
    pub first_note_number: Option<usize>,
    /// Whether the item is within `near-note-distance` to the previous citation
    /// of the same item.
    pub is_near_note: bool,
    /// A forced position from the citation item, overriding the position
    /// derived from citation order.
    pub position: Option<CitePosition>,
    /// A forced near-note state from the citation item, overriding the state
    /// derived from the note numbers.
    pub near_note: Option<bool>,
    /// Whether this citation is the first citation of the entry.
    ///
    /// Only depends on insertion order. The entry cannot be switched with
    /// itself during cite grouping.
    pub is_first: bool,
    /// The index of the item in the original citation request.
    pub initial_idx: usize,
}

impl CertainCiteProperties {
    fn new() -> Self {
        Self::default()
    }

    /// Whether this item is at the first position, honoring a forced position
    /// override (mirrors the `position="first"` choose test).
    fn is_first_position(&self) -> bool {
        self.position.map_or(self.is_first, |p| p == CitePosition::First)
    }
}

/// Item properties that can only be determined after one or multiple renders.
/// These require validation.
#[derive(Debug, Clone, PartialEq)]
struct SpeculativeCiteProperties<'a> {
    /// Locator with its type.
    ///
    /// This will be none during the first render because it would interfere
    /// with disambiguation otherwise.
    pub locator: Option<SpecificLocator<'a>>,
    /// The position the item appears at in the bibliography.
    ///
    /// We can determine this using bibliography sort and cite order once we
    /// have seen all cites.
    pub citation_number: usize,
    /// Whether this citation is exactly the same as the previous citation.
    ///
    /// Although cite ordering is well-defined, grouping occurs only after the
    /// first render and can change the order.
    pub ibid: IbidState,
    /// Whether this citation is a disambiguation.
    ///
    /// Is always false for the first set of renders. Only the rendered entries
    /// allow us to determine if we need to disambiguate.
    pub disambiguation: DisambiguateState,
    /// The disambiguation year suffix assigned to this item (`a`, `b`, …).
    pub year_suffix: Option<u8>,
    /// Whether this citation includes an identifier.
    pub identifier_usage: IdentifierUsage,
}

impl<'a> SpeculativeCiteProperties<'a> {
    /// We can guess about the [`IbidState`] under the assumption that neither
    /// this item nor its predecessors will be subject to cite grouping.
    fn speculate(
        locator: Option<SpecificLocator<'a>>,
        citation_number: usize,
        ibid: IbidState,
    ) -> Self {
        Self {
            locator,
            citation_number,
            ibid,
            disambiguation: DisambiguateState::default(),
            year_suffix: None,
            identifier_usage: IdentifierUsage::default(),
        }
    }

    /// Get the speculative cite properties for a bibliography entry.
    fn for_bibliography(&self) -> Self {
        Self {
            locator: None,
            citation_number: self.citation_number,
            ibid: self.ibid,
            // Name disambiguation applies to cites only.
            disambiguation: match self.disambiguation.clone() {
                DisambiguateState::NameDisambiguation(_) => DisambiguateState::None,
                other => other,
            },
            year_suffix: self.year_suffix,
            identifier_usage: self.identifier_usage,
        }
    }
}

/// Which type of citation label was used when this entry was cited.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum IdentifierUsage {
    /// No label was used.
    #[default]
    None,
    /// Only the alphanumeric citation label was used.
    OnlyCitationLabel,
    /// Only the citation number was used.
    OnlyCitationNumber,
    /// Both the alphanumeric citation label and the citation number were used.
    Mixed,
}

impl IdentifierUsage {
    /// Return the identifier usage given that a label was used.
    fn label(self) -> Self {
        match self {
            Self::None | Self::OnlyCitationLabel => Self::OnlyCitationLabel,
            Self::OnlyCitationNumber | Self::Mixed => Self::Mixed,
        }
    }

    /// Return the identifier usage given that a number was used.
    fn number(self) -> Self {
        match self {
            Self::None | Self::OnlyCitationNumber => Self::OnlyCitationNumber,
            Self::OnlyCitationLabel | Self::Mixed => Self::Mixed,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub enum DisambiguateState {
    #[default]
    None,
    NameDisambiguation(NameDisambiguationProperties),
    /// `cs:choose disambiguate="true"` is active up to the given level.
    Choose(u8),
}

impl DisambiguateState {
    /// Name disambiguation can be iterated upon, so we can stay here.
    fn may_disambiguate_names(&self) -> bool {
        matches!(self, Self::None | Self::NameDisambiguation(_))
    }

    /// Whether another disambiguation level may be activated.
    fn may_disambiguate_with_choose(&self) -> bool {
        matches!(self, Self::None | Self::NameDisambiguation(_) | Self::Choose(_))
    }

    /// Return the more advanced disambiguation state between the two.
    fn max(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, other) => other,
            (self_, Self::None) => self_,
            (Self::NameDisambiguation(a), Self::NameDisambiguation(b)) => {
                Self::NameDisambiguation(a.max(b))
            }
            (Self::NameDisambiguation(_), other) => other,
            (self_, Self::NameDisambiguation(_)) => self_,
            (Self::Choose(a), Self::Choose(b)) => Self::Choose(a.max(b)),
            (Self::Choose(_), other) => other,
            (self_, Self::Choose(_)) => self_,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IbidState {
    /// The previous cite referenced another entry, or this cite has no locator
    /// when the previous one did.
    Different,
    /// The previous cite referenced the same entry, but with a different
    /// locator.
    IbidWithLocator,
    /// The previous cite referenced the same entry with the same locator.
    Ibid,
}

impl IbidState {
    fn with_last<T>(this: &CitationItem<T>, last: Option<&CitationItem<T>>) -> Self
    where
        T: EntryLike + PartialEq,
    {
        if let Some(last) = last {
            if last.entry == this.entry && !last.hidden {
                if last.locator == this.locator {
                    IbidState::Ibid
                } else if this.locator.is_none() {
                    // Per CSL spec: "Preceding cite does have a locator: (...)
                    // If the current cite lacks a locator its only position is
                    // 'subsequent'."
                    IbidState::Different
                } else {
                    // - Both have locators, but they differ
                    // - Previous one has no locator, this one does
                    IbidState::IbidWithLocator
                }
            } else {
                IbidState::Different
            }
        } else {
            IbidState::Different
        }
    }
}

/// This struct allows to add context to where the information in a cite is
/// found in the source.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecificLocator<'a>(pub Locator, pub LocatorPayload<'a>);

/// The type of content a `cs:text` element should yield for a locator.
#[derive(Debug, Clone, PartialEq)]
pub enum LocatorPayload<'a> {
    /// Just print the string.
    Str(&'a str),
    /// An element with the original index of the locator will be yielded. The
    /// consumer can then recognize this and replace it with their own content.
    Transparent(TransparentLocator),
}

/// Wraps an object that is used to determine whether two locators are the same.
#[derive(Clone)]
pub struct TransparentLocator(Arc<dyn TransparentLocatorPayload>);

impl TransparentLocator {
    /// Creates a new [`TransparentLocator`] which wraps the given payload.
    pub fn new<T: PartialEq + 'static>(payload: T) -> Self {
        Self(Arc::new(payload))
    }
}

impl std::fmt::Debug for TransparentLocator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("TransparentLocator").finish_non_exhaustive()
    }
}

impl PartialEq for TransparentLocator {
    fn eq(&self, other: &Self) -> bool {
        TransparentLocatorPayload::dyn_eq(self.0.as_ref(), other.0.as_ref())
    }
}

trait TransparentLocatorPayload: Any {
    fn dyn_eq(&self, other: &dyn TransparentLocatorPayload) -> bool;
}

impl<T: PartialEq + 'static> TransparentLocatorPayload for T {
    fn dyn_eq(&self, other: &dyn TransparentLocatorPayload) -> bool {
        Some(self) == (other as &dyn Any).downcast_ref::<Self>()
    }
}

impl<'a, T: EntryLike> Context<'a, T> {
    /// Whether a term rendered now should be capitalized to start a sentence.
    ///
    /// Mirrors citeproc-js: the first term of a note-style citation is
    /// capitalized unless the citation item carries a prefix that does not
    /// itself look like the start of a new sentence (i.e. it does not end in
    /// terminal punctuation after at least one space).
    fn should_capitalize_term(&self) -> bool {
        !self.bibliography
            && self.style.csl.settings.class == StyleClass::Note
            && (self.cite_prefix.is_some_and(prefix_starts_sentence)
                || (self.instance.cite_props.certain.initial_idx == 0
                    && self.cite_prefix.is_none_or(prefix_starts_sentence)))
    }

    /// Whether the text already written ends a sentence (ignoring trailing
    /// whitespace and closing quotation marks): a term after an item prefix
    /// like `. He said “Please work.” ` starts a new sentence.
    fn last_text_ends_sentence(&self) -> bool {
        let mut text = self.writing.buf.as_string().to_string();
        if text.is_empty() {
            let mut children = self.writing.elem_stack.last().clone();
            if let Some(last) = last_text_mut_child(&mut children.0) {
                text = last.text.clone();
            }
        }
        let mut chars = text.chars().rev().peekable();
        while let Some(c) = chars.next() {
            if c.is_whitespace() {
                continue;
            }
            if matches!(c, '"' | '\'' | '\u{201d}' | '\u{2019}' | '\u{00bb}') {
                continue;
            }
            return matches!(c, '.' | '!' | '?');
        }
        false
    }

    /// Push a format on top of the stack if it is not empty.
    fn push_format(&mut self, format: citationberg::Formatting) -> FormatIdx {
        self.writing.push_format(format)
    }

    /// Pop a format from the stack if it is not empty.
    fn pop_format(&mut self, pos: FormatIdx) {
        self.writing.pop_format(pos)
    }

    /// Add another subtree to the children element. This must be done to
    /// include a new element or to check that the subtree is empty.
    fn push_elem(&mut self, format: citationberg::Formatting) -> DisplayLoc {
        self.writing.push_elem(format)
    }

    /// Like [`Self::push_elem`], but records the declared formatting on the
    /// resulting element while rendering a bibliography entry. Serializers
    /// use it to reproduce citeproc-js's tags for a formatting declaration.
    fn push_scoped_elem(&mut self, format: citationberg::Formatting) -> DisplayLoc {
        let mut loc = self.writing.push_elem(format);
        if self.bibliography {
            loc.2 = Formatting::default().apply(format);
        }
        loc
    }

    /// Remove the last subtree and discard it.
    ///
    /// Will panic if the location does not match.
    fn discard_elem(&mut self, loc: DisplayLoc) {
        self.writing.discard_elem(loc)
    }

    /// Nest the last subtree into its ancestor. If the `display` argument is
    /// some, a new element child will be created there. Otherwise, we will
    /// append the children of the last subtree to the children of its ancestor.
    fn commit_elem(
        &mut self,
        loc: DisplayLoc,
        display: Option<Display>,
        meta: Option<ElemMeta>,
    ) {
        self.writing.commit_elem(loc, display, meta)
    }

    /// Nest the last subtree into its ancestor, prepending `delimiter` when
    /// the subtree rendered content. Returns whether it did.
    fn commit_elem_with_delimiter(
        &mut self,
        loc: DisplayLoc,
        delimiter: Option<&str>,
    ) -> bool {
        self.writing.commit_elem_with_delimiter(loc, delimiter)
    }

    /// Ensure that the buffer is either empty or the last character is a space.
    pub fn ensure_space(&mut self) {
        self.writing.ensure_space()
    }

    /// The last character rendered so far, if any.
    fn last_char(&mut self) -> Option<char> {
        self.writing.save_to_block();
        if let Some(c) = self.writing.buf.as_string_mut().chars().next_back() {
            return Some(c);
        }
        self.writing
            .elem_stack
            .last_mut_predicate(|p| !p.is_empty())
            .and_then(|p| p.last_text_mut())
            .and_then(|t| t.text.chars().next_back())
    }

    /// Add the appropriate opening quotation marks.
    fn push_quotes(&mut self) {
        let marks = QuoteMarks::get(self.style);
        let mark = self.writing.quoter.open_quotes(&marks).to_string();
        self.push_str_raw(&mark);
    }

    /// Add the appropriate closing quotation marks.
    fn pop_quotes(&mut self) {
        let marks = QuoteMarks::get(self.style);
        let mark = self.writing.quoter.close_quotes(&marks).to_string();
        self.push_str_raw(&mark);
    }

    /// Pull punctuation into a quote if applicable
    fn do_pull_punctuation<'s>(&mut self, mut s: &'s str) -> &'s str {
        // Merge the punctuation that follows a closing quotation with the
        // punctuation that ends the quotation (citeproc-js's LtoR_MAP). The
        // merged characters are split at the quote mark: `swap-in`
        // punctuation (`.`, `,`, `!`, `?`) stays inside, `swap-out`
        // punctuation (`:`, `;`) stays outside
        // (`punctuation_FullMontyQuotesIn`).
        if self.style.punctuation_in_quotes()
            && let Some(first) = s.chars().next()
            && matches!(first, '.' | ',' | '!' | '?' | ':' | ';')
            && self.merge_quote_punctuation(first)
        {
            return &s[first.len_utf8()..];
        }

        // citeproc-js's punctuation-in-quote only swaps terminal punctuation
        // dot, comma, exclamation and question marks inside the quote;
        // semicolons and colons stay outside (FullMontyQuotesIn).
        if self.writing.pull_punctuation && s.starts_with(['.', ',', '!', '?']) {
            let marks = QuoteMarks::get(self.style);

            let mut used_buf = false;
            let buf = if self.writing.buf.is_empty() {
                self.writing
                    .elem_stack
                    .last_mut_predicate(|p| !p.is_empty())
                    .and_then(|p| p.last_text_mut())
                    .map(|f| &mut f.text)
                    .unwrap_or_else(|| {
                        used_buf = true;
                        self.writing.buf.as_string_mut()
                    })
            } else {
                used_buf = true;
                self.writing.buf.as_string_mut()
            };

            // Check whether the buffer ends in closing quotes. If it does,
            // move the punctuation inside them.
            if quotes::move_punctuation_inside(buf, s.chars().next().unwrap(), &marks) {
                s = &s[s.chars().next().unwrap().len_utf8()..];

                if used_buf {
                    self.writing.buf.mark_changed();
                }
            }
        }

        s
    }

    /// Merge `following` with the punctuation that ends the current
    /// quotation, if the output currently ends with a closing quotation mark.
    ///
    /// Returns whether the merge consumed `following`.
    fn merge_quote_punctuation(&mut self, following: char) -> bool {
        let marks = QuoteMarks::get(self.style);
        let Some(text) = self.writing.last_mut_text() else { return false };

        // A colon or semicolon suffix was rendered outside the closing
        // quotation; it trails the marks.
        let body = text.trim_end_matches([':', ';']);
        let outside = text[body.len()..].chars().next();
        let Some(close_start) = marks.trailing_close_quote_start(body) else {
            return false;
        };
        let inside = body[..close_start]
            .chars()
            .next_back()
            .filter(|c| matches!(c, '.' | ',' | '!' | '?' | ':' | ';'));

        let (left, inside_len) = match outside {
            Some(c) => (c, 0),
            None => match inside {
                Some(c) => (c, c.len_utf8()),
                None => return false,
            },
        };
        // Duplicate punctuation collapses to one mark: the one that already
        // ends the quotation.
        if left == following {
            return true;
        }
        let Some(merged) = quotes::merge_ltr(left, following) else {
            return false;
        };

        // citeproc-js merges to the left and only lets the merged result
        // migrate into the quotation when it starts with `swap-in`
        // punctuation; a result that starts with `:` or `;` stays outside as
        // a whole (`,:` and `;,` in `punctuation_FullMontyQuotesIn`).
        let (inside, outside): (String, String) = if merged
            .chars()
            .next()
            .is_some_and(|c| matches!(c, '.' | ',' | '!' | '?'))
        {
            (
                merged.chars().filter(|c| matches!(c, '.' | ',' | '!' | '?')).collect(),
                merged.chars().filter(|c| matches!(c, ':' | ';')).collect(),
            )
        } else {
            (String::new(), merged.to_string())
        };

        let close_run = &body[close_start..];
        let mut new = String::with_capacity(text.len() + merged.len());
        new.push_str(&body[..close_start - inside_len]);
        new.push_str(&inside);
        new.push_str(close_run);
        new.push_str(&outside);
        *text = new;
        true
    }

    /// Convert the quotation marks in `s` using the current quote state.
    fn smart_quote(&mut self, s: &str) -> String {
        let marks = QuoteMarks::get(self.style);
        self.writing.quoter.apply(s, &marks)
    }

    /// Add a string to the buffer.
    ///
    /// Strings from CSL-JSON variables may contain citeproc-js's rich-text
    /// markup (`<i>`, `<b>`, `<sc>`, `<sup>`, `<sub>`, `<span class="nocase">`
    /// and `<span style="...">`). Tags are turned into formatting scopes and
    /// `nocase` content bypasses case folding; the tags themselves never reach
    /// the output.
    fn push_str(&mut self, s: &str) {
        if !s.contains('<') {
            self.push_str_plain(s);
            return;
        }

        let mut stack: Vec<MarkupOpen> = Vec::new();
        let mut start = 0;
        let mut i = 0;
        let mut any_pushed = false;

        while i < s.len() {
            if s.as_bytes()[i] == b'<' {
                if let Some((len, tag)) = parse_markup_tag(&s[i..]) {
                    let nocase = stack.iter().any(|o| matches!(o, MarkupOpen::NoCase));
                    let mid = any_pushed;
                    any_pushed |= !s[start..i].is_empty();
                    self.push_markup_text(&s[start..i], nocase, mid);
                    self.apply_markup_tag(tag, &mut stack);
                    any_pushed = true;
                    i += len;
                    start = i;
                    continue;
                }
            }
            i += 1;
        }

        let nocase = stack.iter().any(|o| matches!(o, MarkupOpen::NoCase));
        self.push_markup_text(&s[start..], nocase, any_pushed);

        self.close_markup_scopes(&mut stack, 0);
    }

    /// Push a text segment found between rich-text tags.
    ///
    /// `mid` marks segments that continue a string already partly pushed:
    /// their leading whitespace and the preceding trailing whitespace must
    /// survive the case-folder's sentence-start trimming.
    fn push_markup_text(&mut self, text: &str, nocase: bool, mid: bool) {
        if text.is_empty() {
            return;
        }
        if nocase {
            // Verbatim content keeps its own capitalization but still takes
            // part in smart quoting and leaves the case folder inside a word,
            // so following text is not mistaken for a new sentence.
            let normalized = normalize_punctuation_spacing(text);
            let quoted = self.smart_quote(&normalized);
            self.writing.buf.push_verbatim(&quoted);
            self.writing.pull_punctuation = false;
        } else {
            self.push_str_plain_seam(text, mid);
        }
    }

    /// Apply one rich-text tag, recording the scopes it opens.
    fn apply_markup_tag(&mut self, tag: MarkupTag, stack: &mut Vec<MarkupOpen>) {
        match tag {
            MarkupTag::Open(MarkupKind::NoCase) => stack.push(MarkupOpen::NoCase),
            MarkupTag::Open(kind) => {
                let idx = self.push_format(markup_formatting(kind));
                stack.push(MarkupOpen::Format(kind, idx));
            }
            MarkupTag::Close(kind) => {
                // Close the innermost matching scope, tolerating malformed
                // nesting by closing everything opened inside it.
                if let Some(pos) = stack.iter().rposition(|open| open.matches(kind)) {
                    self.close_markup_scopes(stack, pos);
                }
            }
            MarkupTag::CloseSpan => {
                if let Some(pos) = stack.iter().rposition(|open| {
                    matches!(open, MarkupOpen::Span(_) | MarkupOpen::NoCase)
                }) {
                    self.close_markup_scopes(stack, pos);
                }
            }
        }
    }

    fn close_markup_scopes(&mut self, stack: &mut Vec<MarkupOpen>, pos: usize) {
        while stack.len() > pos {
            match stack.pop().unwrap() {
                MarkupOpen::NoCase => {}
                MarkupOpen::Format(_, idx) | MarkupOpen::Span(idx) => {
                    self.pop_format(idx)
                }
            }
        }
    }

    /// Add a string to the buffer without rich-text parsing.
    fn push_str_plain(&mut self, s: &str) {
        self.push_str_plain_seam(s, false)
    }

    fn push_str_plain_seam(&mut self, s: &str, mid: bool) {
        let normalized = normalize_punctuation_spacing(s);
        let quoted = self.smart_quote(&normalized);
        self.push_str_raw_seam(&quoted, mid)
    }

    /// Add a string to the buffer without smart quote conversion.
    fn push_str_raw(&mut self, s: &str) {
        self.push_str_raw_seam(s, false)
    }

    fn push_str_raw_seam(&mut self, s: &str, mid: bool) {
        let s = self.do_pull_punctuation(s);

        if mid {
            self.writing.buf.prevent_trimming();
        }
        self.writing.reconfigure();
        if mid {
            self.writing.buf.prevent_trimming();
        }

        fn last_buffer(ctx: &mut WritingContext) -> Option<&mut String> {
            let last = ctx
                .elem_stack
                .last_mut_predicate(|s| !s.is_empty())
                .and_then(|e| e.last_text_mut());
            if !ctx.buf.is_empty() {
                Some(ctx.buf.as_string_mut())
            } else if let Some(last) = last {
                Some(&mut last.text)
            } else {
                None
            }
        }

        // Only literal spaces collapse at a seam; newlines and tabs are
        // significant delimiters in some styles (e.g. the punctuation tests'
        // blank lines).
        let ends_with_space = last_buffer(&mut self.writing).is_some_and(|s| {
            s.chars().next_back().is_some_and(|c| matches!(c, ' ' | '\u{a0}'))
        });

        // Collapse duplicated whitespace at a seam. citeproc-js keeps a
        // single trailing space before punctuation that follows as its own
        // string (`(n.d.) .` in `bugreports_NoTitle`), so only a following
        // space is eaten here.
        if ends_with_space
            && s.chars().next().is_some_and(|c| matches!(c, ' ' | '\u{a0}'))
            && let Some(buf) = last_buffer(&mut self.writing)
        {
            buf.truncate(buf.trim_end_matches([' ', '\u{a0}']).len());
        }

        // Do not print duplicate affixes.
        if s.chars().all(|c| !c.is_alphabetic()) {
            let trimmed = s.trim_end();
            if let Some(last) = last_buffer(&mut self.writing)
                && let Some(strip) = last.strip_suffix(trimmed)
            {
                last.truncate(strip.len());
            }
        }

        if self.writing.strip_periods {
            // Replicate citeproc.js behavior: remove a period if the
            // preceding character in the original string is not a period.
            let mut last_period = false;
            for c in s.chars() {
                let is_period = c == '.';
                if !is_period || last_period {
                    self.writing.buf.push(c);
                }
                last_period = is_period;
            }
        } else {
            self.writing.buf.push_str(s);
        }

        self.writing.pull_punctuation = false;
    }

    /// Push a chunked string to the buffer.
    pub fn push_chunked(&mut self, chunked: &ChunkedString) {
        for chunk in &chunked.0 {
            match chunk.kind {
                ChunkKind::Normal => self.push_str(&chunk.value),
                ChunkKind::Verbatim => {
                    self.writing.buf.push_verbatim(&chunk.value);
                    self.writing.pull_punctuation = false;
                }
                ChunkKind::Math => {
                    self.writing.buf.prevent_trimming();
                    self.writing.save_to_block();
                    self.writing
                        .elem_stack
                        .last_mut()
                        .0
                        .push(ElemChild::Markup(chunk.value.clone()));
                    self.writing.reconfigure();
                    self.writing.buf.prevent_trimming();
                }
            }
        }
    }

    /// Push a link into the buffer.
    pub fn push_link(&mut self, chunked: &ChunkedString, url: String) {
        let format = *self.writing.formatting();
        self.writing.save_to_block();
        self.writing
            .elem_stack
            .last_mut()
            .0
            .push(ElemChild::Link { text: format.add_text(chunked.to_string()), url })
    }

    /// Push a transparent element child into the buffer.
    pub fn push_transparent(&mut self, idx: usize) {
        let format = *self.writing.formatting();
        self.writing.save_to_block();
        self.writing
            .elem_stack
            .last_mut()
            .0
            .push(ElemChild::Transparent { cite_idx: idx, format })
    }

    /// Folds all remaining elements into the first element and returns it.
    fn flush(self) -> ElemChildren {
        self.writing.flush()
    }

    /// Get a term from the style.
    /// The raw locator string, when the cite carries a string locator.
    fn locator_string(&self) -> Option<&str> {
        match &self.instance.cite_props.speculative.locator.as_ref()?.1 {
            LocatorPayload::Str(s) => Some(s),
            LocatorPayload::Transparent(_) => None,
        }
    }

    /// The locator label, taking a label embedded at the start of the
    /// locator string into account (`vol. 1` with the default `page` label is
    /// a volume locator).
    fn effective_locator_label(&self) -> Option<Locator> {
        let locator = &self.instance.cite_props.speculative.locator.as_ref()?.0;
        if *locator == Locator::Page
            && let Some(s) = self.locator_string()
            && let Some((label, _)) = split_embedded_locator_label(s)
        {
            return Some(label);
        }
        Some(*locator)
    }

    /// The locator string without an embedded leading label.
    fn locator_display_text(&self) -> Option<&str> {
        let s = self.locator_string()?;
        let original = &self.instance.cite_props.speculative.locator.as_ref()?.0;
        if *original == Locator::Page
            && let Some((_, rest)) = split_embedded_locator_label(s)
        {
            return Some(rest);
        }
        Some(s)
    }

    /// Whether the locator label is a page label.
    fn locator_is_page(&self) -> bool {
        self.effective_locator_label() == Some(Locator::Page)
    }

    /// citeproc-js's contextual pluralization for a locator string.
    fn locator_is_plural(&self) -> bool {
        let Some(s) = self.locator_string() else { return false };
        let effective = self.effective_locator_label();
        let text = self.locator_display_text().unwrap_or(s);
        if effective == Some(Locator::Page) {
            return page_string_is_plural(text, self);
        }
        crate::csl::rendering::string_has_numeric_range(text)
    }

    /// Render locator text with embedded-label stripping, page-range
    /// formatting and citeproc's ampersand localization.
    fn push_locator_text(&mut self, fallback: &str) {
        let text = self.locator_display_text().unwrap_or(fallback).trim().to_string();
        let localized_and = self
            .term(Term::Other(OtherTerm::And), TermForm::Long, false)
            .unwrap_or("and")
            .to_string();
        let symbol_and = self
            .term(Term::Other(OtherTerm::And), TermForm::Symbol, false)
            .unwrap_or("&")
            .to_string();
        let amp = if localized_and == symbol_and { "&".to_string() } else { symbol_and };
        let text = format_page_string(&text, self, self.locator_is_page());
        let text =
            if amp != "&" { text.replace(" & ", &format!(" {amp} ")) } else { text };
        self.push_str(&text);
    }

    fn term(&self, mut term: Term, form: TermForm, plural: bool) -> Option<&'a str> {
        if term == Term::NumberVariable(csl_taxonomy::NumberVariable::Locator)
            && let Some(locator) = self.effective_locator_label()
        {
            term = locator.into();
        }

        let mut form = Some(form);
        while let Some(current_form) = form {
            if let Some(localization) = self.style.lookup_locale(|l| {
                let term = l.term(term, current_form)?;
                Some(if plural { term.multiple() } else { term.single() })
            }) {
                return localization;
            }

            form = current_form.fallback();
        }

        None
    }

    /// Get the gender of a term.
    fn gender(&self, term: Term) -> Option<GrammarGender> {
        if let Some(localization) =
            self.style.lookup_locale(|l| l.term(term, TermForm::default()))
        {
            localization.gender
        } else {
            None
        }
    }

    /// Get a localized date format.
    fn localized_date(&self, form: DateForm) -> Option<&'a citationberg::Date> {
        self.style
            .lookup_locale(|l| l.date.iter().find(|d| d.form == Some(form)))
    }

    /// Get the ordinal lookup object.
    fn ordinal_lookup(&self) -> OrdinalLookup<'a> {
        self.style
            .lookup_locale(|l| l.ordinals())
            .unwrap_or_else(OrdinalLookup::empty)
    }

    /// Pull the next punctuation character into the preceding quoted content
    /// if appropriate for the locale.
    fn may_pull_punctuation(&mut self) {
        self.writing.pull_punctuation |= self.style.punctuation_in_quotes();
    }

    /// Set whether to strip periods.
    fn may_strip_periods(&mut self, strip: bool) {
        self.writing.may_strip_periods(strip)
    }

    /// Stop stripping periods.
    fn stop_stripping_periods(&mut self) {
        self.writing.stop_stripping_periods()
    }

    /// Set the case of the next text.
    fn push_case(&mut self, case: Option<TextCase>) -> CaseIdx {
        if case.is_none_or(|c| c.is_language_independent())
            || self
                .instance
                .entry
                .is_english()
                .or_else(|| self.instance.locale.map(LocaleCode::is_english))
                .or_else(|| self.instance.term_locale.map(LocaleCode::is_english))
                .or_else(|| {
                    self.style.csl.default_locale.as_ref().map(LocaleCode::is_english)
                })
                .unwrap_or(true)
        {
            // Turkish and Azeri casing is locale-dependent even for the
            // language-independent `uppercase`/`lowercase` transforms
            // (`i` uppercases to `İ`, `I` lowercases to `ı`).
            let turkic = self
                .instance
                .locale
                .map(|locale| locale.0.clone())
                .or_else(|| self.instance.entry.language().map(Cow::into_owned))
                .is_some_and(|locale| {
                    locale.split(['-', '_']).next().is_some_and(|lang| {
                        lang.eq_ignore_ascii_case("tr") || lang.eq_ignore_ascii_case("az")
                    })
                });
            let case = case.map(|case| match (case, turkic) {
                (TextCase::Uppercase, true) => Case::UppercaseTurkic,
                (TextCase::Lowercase, true) => Case::LowercaseTurkic,
                _ => case.into(),
            });
            self.writing.push_case(case)
        } else {
            self.writing.push_case(None)
        }
    }

    /// Clear the case of the next text.
    fn pop_case(&mut self, idx: CaseIdx) {
        self.writing.pop_case(idx)
    }

    /// Resolve a number variable.
    ///
    /// Honors suppressions.
    fn resolve_number_variable(
        &self,
        variable: NumberVariable,
    ) -> Option<NumberVariableResult<'a>> {
        // Replace the citation label with citation number if necessary.
        if variable == NumberVariable::CitationNumber {
            if self.bibliography {
                if matches!(
                    *self.instance.identifier_usage.borrow(),
                    IdentifierUsage::OnlyCitationLabel
                ) {
                    return self
                        .instance
                        .resolve_standard_variable(
                            LongShortForm::default(),
                            StandardVariable::CitationLabel,
                        )
                        .map(|c| {
                            NumberVariableResult::Regular(MaybeTyped::String(
                                c.to_string(),
                            ))
                        });
                }
            } else {
                *self.instance.identifier_usage.borrow_mut() =
                    self.instance.identifier_usage.take().number();
            }
        }

        self.writing.prepare_variable_query(variable)?;

        self.instance.resolve_number_variable(variable)
    }

    fn resolve_page_variable(
        &self,
        variable: PageVariable,
    ) -> Option<PageVariableResult> {
        self.writing.prepare_variable_query(variable)?;
        self.instance.resolve_page_variable(variable)
    }

    fn resolve_number_or_page_variable(
        &self,
        variable: NumberOrPageVariable,
    ) -> Option<NumberOrPageVariableResult<'a>> {
        match variable {
            NumberOrPageVariable::Page(p) => {
                self.resolve_page_variable(p).map(NumberOrPageVariableResult::Page)
            }
            NumberOrPageVariable::Number(n) => self
                .resolve_number_variable(n)
                .map(NumberOrPageVariableResult::Number),
        }
    }

    /// Resolve a name variable.
    ///
    /// Honors suppressions.
    fn resolve_standard_variable(
        &self,
        form: LongShortForm,
        variable: csl_taxonomy::StandardVariable,
    ) -> Option<Cow<'a, ChunkedString>> {
        // Replace the citation label with citation number if necessary.
        if variable == StandardVariable::CitationLabel {
            if self.bibliography {
                if matches!(
                    *self.instance.identifier_usage.borrow(),
                    IdentifierUsage::OnlyCitationNumber
                ) {
                    return self
                        .instance
                        .resolve_number_variable(NumberVariable::CitationNumber)
                        .map(|n| match n {
                            NumberVariableResult::Regular(n) => {
                                Cow::Owned(ChunkedString::from(n.to_string()))
                            }
                            NumberVariableResult::Transparent(_) => {
                                panic!("unexpected transparent")
                            }
                        });
                }
            } else {
                *self.instance.identifier_usage.borrow_mut() =
                    self.instance.identifier_usage.take().label();
            }
        }

        self.writing.prepare_variable_query(variable)?;

        self.instance.resolve_standard_variable(form, variable)
    }

    /// Resolve a date variable.
    ///
    /// Honors suppressions.
    fn resolve_date_variable(
        &self,
        variable: csl_taxonomy::DateVariable,
    ) -> Option<Cow<'a, Date>> {
        self.writing.prepare_variable_query(variable)?;

        self.instance.entry.resolve_date_variable(variable)
    }

    /// Resolve a literal date value (`"in press"`) for a date variable.
    ///
    /// Honors suppressions like [`Self::resolve_date_variable`].
    fn resolve_date_literal(
        &self,
        variable: csl_taxonomy::DateVariable,
    ) -> Option<Cow<'a, str>> {
        self.writing.prepare_variable_query(variable)?;

        self.instance.entry.resolve_date_literal(variable)
    }

    /// Resolve a name variable.
    ///
    /// Honors suppressions.
    fn resolve_name_variable(
        &self,
        variable: csl_taxonomy::NameVariable,
    ) -> Vec<Cow<'a, Person>> {
        if self.writing.prepare_variable_query(variable).is_none() {
            return Vec::new();
        }

        self.instance.entry.resolve_name_variable(variable)
    }

    /// Apply a prefix, but return a tuple that allows us to undo it if it
    /// wasn't followed by anything.
    ///
    /// `ambient` is the formatting that was in effect before the element's
    /// own formatting was applied.
    fn apply_prefix(
        &mut self,
        affixes: &Affixes,
        ambient: Formatting,
    ) -> (DisplayLoc, usize) {
        // Smart-quote the prefix and pull leading punctuation into a
        // preceding quotation before it is written.
        let mut affixes = affixes.clone();
        if let Some(prefix) = affixes.prefix.take() {
            // citeproc-js appends affixes verbatim: quote marks in an affix
            // are never flip-flopped (`quotes_QuotesUnderQuotesFalse`).
            affixes.prefix = Some(self.do_pull_punctuation(&prefix).to_string());
        }
        self.writing.apply_prefix(&affixes, ambient)
    }

    /// Apply a suffix, but only if the location was followed by something.
    /// Delete any prefix if not.
    ///
    /// `ambient` is the formatting that was in effect before the element's
    /// own formatting was applied.
    /// Apply the bibliography layout suffix. citeproc-js migrates trailing
    /// layout punctuation into the last display block (`second-field-align`
    /// right-inline or `display` block), so the period belongs to that div.
    fn apply_bibliography_suffix(
        &mut self,
        affixes: &Affixes,
        loc: (DisplayLoc, usize),
        ambient: Formatting,
    ) {
        if let Some(suffix) = &affixes.suffix {
            self.writing.save_to_block();
            let last_display =
                self.writing.elem_stack.last_mut().0.last_mut().and_then(|child| {
                    match child {
                        ElemChild::Elem(e) if e.display.is_some() => Some(e),
                        _ => None,
                    }
                });
            if let Some(elem) = last_display {
                let mut current = String::new();
                for child in &elem.children.0 {
                    if let ElemChild::Text(t) = child {
                        current.push_str(&t.text);
                    }
                }
                let mut suffix = suffix.clone();
                let marks = QuoteMarks::get(self.style);
                move_punctuation_inside_quote(
                    &mut elem.children,
                    &mut suffix,
                    self.style.punctuation_in_quotes(),
                    &marks,
                );
                if !suffix.is_empty() && !current.ends_with(suffix.as_str()) {
                    elem.children.0.push(ElemChild::Text(ambient.add_text(suffix)));
                }
                self.commit_elem(loc.0, None, None);
                return;
            }
        }
        self.apply_suffix(affixes, loc, ambient);
    }

    fn apply_suffix(
        &mut self,
        affixes: &Affixes,
        loc: (DisplayLoc, usize),
        ambient: Formatting,
    ) {
        if !self.writing.has_content_since(&loc) {
            self.discard_elem(loc.0);
        } else {
            if let Some(suffix) = &affixes.suffix {
                let do_suffix = if !self.writing.buf.is_empty() {
                    !self.writing.buf.as_string_mut().ends_with(suffix.as_str())
                } else if let Some(l) = self.writing.elem_stack.last_mut().last_text() {
                    !l.text.ends_with(suffix)
                } else {
                    true
                };

                if do_suffix {
                    if self.style.punctuation_in_quotes()
                        && suffix.starts_with(['.', ',', '!', '?'])
                        && self.last_char().is_some_and(|c| {
                            matches!(c, '"' | '\'' | '\u{201d}' | '\u{2019}' | '\u{00bb}')
                        })
                    {
                        self.writing.pull_punctuation = true;
                    }
                    self.push_affix_str(suffix, ambient);
                }
            }
            self.commit_elem(loc.0, None, None);
        }
    }

    /// Push an affix string, like [`Self::push_str`], but if the element
    /// re-declared formatting, the buffered content is flushed first and the
    /// affix is written as its own run under `ambient`, the element's
    /// ancestor formatting.
    fn push_affix_str(&mut self, s: &str, ambient: Formatting) {
        if ambient == *self.writing.formatting() {
            self.push_str_affix(s);
            return;
        }

        self.writing.save_to_block();
        let prev = mem::replace(self.writing.format_stack.last_mut(), ambient);
        self.push_str_affix(s);
        self.writing.save_to_block();
        *self.writing.format_stack.last_mut() = prev;
    }

    /// Push literal affix text: no smart-quote conversion (citeproc-js leaves
    /// affix quotes straight), but punctuation-in-quote and seam merging
    /// still apply.
    fn push_str_affix(&mut self, s: &str) {
        let normalized = normalize_punctuation_spacing(s);
        self.push_str_raw_seam(&normalized, false);
    }

    /// Test whether this entry should disambiguate via `cs:choose`.
    fn should_disambiguate(&mut self) -> bool {
        self.writing.checked_disambiguate = true;
        let level = match self.instance.cite_props.speculative.disambiguation {
            DisambiguateState::Choose(level) => level,
            _ => 0,
        };
        // citeproc-js counts the `disambiguate="true"` conditions as they are
        // evaluated: the Nth condition is true when the item's disambiguation
        // level is at least N, which makes `cs:choose` levels incremental.
        if self.writing.disambiguate_count < level {
            self.writing.disambiguate_count += 1;
            true
        } else {
            false
        }
    }

    /// Check whether this is the first date and set the first date flag.
    fn is_first_date(&mut self) -> bool {
        let res = self.writing.first_date;
        self.writing.first_date = false;
        res
    }

    /// Check whether this is the first date.
    fn peek_is_first_date(&self) -> bool {
        self.writing.first_date
    }

    /// Whether the style renders the `year-suffix` variable explicitly.
    fn renders_explicit_year_suffix(&mut self) -> bool {
        self.style
            .csl
            .citation
            .layout
            .will_render(self, StandardVariable::YearSuffix.into())
            || self.style.csl.bibliography.as_ref().is_some_and(|b| {
                b.layout.will_render(self, StandardVariable::YearSuffix.into())
            })
    }

    /// Checks that neither the bibliography nor the citation layout render the
    /// year suffix (and that no citation label carries it instead).
    fn renders_year_suffix_implicitly(&mut self) -> bool {
        !uses_citation_label(&self.style) && !self.renders_explicit_year_suffix()
    }

    /// Set the [`SpecialForm`]
    fn set_special_form(&mut self, form: Option<SpecialForm>) {
        self.instance.kind = form;
    }
}

#[must_use = "format stack must be popped"]
struct FormatIdx(NonZeroUsize);

#[must_use = "element stack must be popped"]
struct DisplayLoc(NonZeroUsize, FormatIdx, Formatting);

impl DisplayLoc {
    fn new(pos: NonZeroUsize, format_idx: FormatIdx, formatting: Formatting) -> Self {
        Self(pos, format_idx, formatting)
    }
}

#[must_use = "case stack must be popped"]
struct CaseIdx(NonZeroUsize);

#[must_use = "delimiter stack must be popped"]
struct DelimiterIdx(NonZeroUsize);

/// A rich-text tag kind from CSL-JSON input (citeproc-js's accepted HTML
/// subset).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MarkupKind {
    Italic,
    Bold,
    SmallCaps,
    Underline,
    Sup,
    Sub,
    NoCase,
    NoDecor,
}

/// A rich-text scope opened by a tag in an input string.
enum MarkupOpen {
    NoCase,
    Format(MarkupKind, FormatIdx),
    Span(FormatIdx),
}

impl MarkupOpen {
    fn matches(&self, kind: MarkupKind) -> bool {
        match self {
            MarkupOpen::NoCase => kind == MarkupKind::NoCase,
            MarkupOpen::Format(open, _) => *open == kind,
            MarkupOpen::Span(_) => false,
        }
    }
}

/// A parsed rich-text tag: either an opening or a closing tag.
enum MarkupTag {
    Open(MarkupKind),
    Close(MarkupKind),
    /// `</span>` closes the innermost span scope, whatever it declared.
    CloseSpan,
}

/// Formatting applied by a rich-text tag.
fn markup_formatting(kind: MarkupKind) -> citationberg::Formatting {
    use citationberg::{
        FontStyle, FontVariant, FontWeight, Formatting, TextDecoration, VerticalAlign,
    };

    let mut formatting = Formatting::default();
    match kind {
        MarkupKind::Italic => formatting.font_style = Some(FontStyle::Italic),
        MarkupKind::Bold => formatting.font_weight = Some(FontWeight::Bold),
        MarkupKind::SmallCaps => formatting.font_variant = Some(FontVariant::SmallCaps),
        MarkupKind::Underline => {
            formatting.text_decoration = Some(TextDecoration::Underline)
        }
        MarkupKind::Sup => formatting.vertical_align = Some(VerticalAlign::Sup),
        MarkupKind::Sub => formatting.vertical_align = Some(VerticalAlign::Sub),
        MarkupKind::NoDecor => return nodecor_formatting(),
        MarkupKind::NoCase => {}
    }
    formatting
}

/// Formatting that nullifies any inherited decoration (`nodecor`).
fn nodecor_formatting() -> citationberg::Formatting {
    use citationberg::{
        FontStyle, FontVariant, FontWeight, Formatting, TextDecoration, VerticalAlign,
    };

    Formatting {
        font_style: Some(FontStyle::Normal),
        font_variant: Some(FontVariant::Normal),
        font_weight: Some(FontWeight::Normal),
        text_decoration: Some(TextDecoration::None),
        vertical_align: Some(VerticalAlign::Baseline),
    }
}

/// citeproc-js normalizes French punctuation spacing in every appended
/// string: a space before `:`, `;`, `?`, `!` or `»` becomes a narrow
/// no-break space, and the space after `«` becomes one as well.
fn normalize_punctuation_spacing(s: &str) -> Cow<'_, str> {
    if !s.contains([':', ';', '?', '!', '\u{00ab}', '\u{00bb}']) {
        return Cow::Borrowed(s);
    }

    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            ':' | ';' | '?' | '!' | '\u{00bb}' if out.ends_with(' ') => {
                out.pop();
                out.push('\u{202f}');
                out.push(c);
            }
            _ => out.push(c),
        }
    }

    let out = out.replace("\u{00ab} ", "\u{00ab}\u{202f}");
    Cow::Owned(out)
}

/// Parse a rich-text tag at the start of `s`, returning its length and the
/// scope it opens or closes.
///
/// Recognized tags mirror citeproc-js's CSL-JSON markup: `<i>`, `<b>`, `<sc>`,
/// `<sup>`, `<sub>`, `<span class="nocase">`/`<span class="nodecor">` and
/// `<span style="...">` with the CSS properties citeproc-js understands.
fn parse_markup_tag(s: &str) -> Option<(usize, MarkupTag)> {
    if !s.starts_with('<') {
        return None;
    }

    let close = s.starts_with("</");
    let body_start = if close { 2 } else { 1 };
    let end = s[body_start..].find('>')? + body_start;
    let mut body = &s[body_start..end];
    let len = end + 1;
    if let Some(stripped) = body.strip_suffix('/') {
        body = stripped.trim_end();
    }

    if body == "span" {
        return if close { Some((len, MarkupTag::CloseSpan)) } else { None };
    }

    if let Some(rest) = body.strip_prefix("span") {
        if close {
            return Some((len, MarkupTag::CloseSpan));
        }
        if let Some(class) = attribute_value(rest, "class") {
            let kind = match class.trim() {
                "nocase" => MarkupKind::NoCase,
                "nodecor" => MarkupKind::NoDecor,
                _ => return None,
            };
            return Some((len, MarkupTag::Open(kind)));
        }
        if let Some(style) = attribute_value(rest, "style") {
            let kind = parse_css_formatting(style)?;
            return Some((len, MarkupTag::Open(kind)));
        }
        return None;
    }

    let kind = match body {
        "i" => MarkupKind::Italic,
        "b" => MarkupKind::Bold,
        "sc" => MarkupKind::SmallCaps,
        "sup" => MarkupKind::Sup,
        "sub" => MarkupKind::Sub,
        _ => return None,
    };
    Some((len, if close { MarkupTag::Close(kind) } else { MarkupTag::Open(kind) }))
}

/// Map the CSS declarations citeproc-js accepts in `style` attributes to a
/// markup kind. Only the first recognized declaration is used.
fn parse_css_formatting(style: &str) -> Option<MarkupKind> {
    for declaration in style.split(';') {
        let Some((property, value)) = declaration.split_once(':') else {
            continue;
        };
        let property = property.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        let kind = match (property.as_str(), value.as_str()) {
            ("font-style", "italic" | "oblique") => MarkupKind::Italic,
            ("font-variant", "small-caps") => MarkupKind::SmallCaps,
            ("font-weight", "bold") => MarkupKind::Bold,
            ("text-decoration", "underline") => MarkupKind::Underline,
            ("vertical-align", "sup" | "super") => MarkupKind::Sup,
            ("vertical-align", "sub" | "subscript") => MarkupKind::Sub,
            ("font-style" | "font-variant" | "font-weight", "normal")
            | ("vertical-align", "baseline") => MarkupKind::NoDecor,
            _ => continue,
        };
        return Some(kind);
    }
    None
}

/// The value of an HTML attribute (double- or single-quoted).
fn attribute_value<'a>(tag: &'a str, name: &str) -> Option<&'a str> {
    let mut rest = tag.trim_start();
    while !rest.is_empty() {
        let eq = rest.find('=')?;
        let key = rest[..eq].trim();
        let after = rest[eq + 1..].trim_start();
        let (value, remaining) = if let Some(after) = after.strip_prefix('"') {
            let end = after.find('"')?;
            (&after[..end], &after[end + 1..])
        } else if let Some(after) = after.strip_prefix('\'') {
            let end = after.find('\'')?;
            (&after[..end], &after[end + 1..])
        } else {
            let end = after.find(char::is_whitespace).unwrap_or(after.len());
            (&after[..end], &after[end..])
        };
        if key.eq_ignore_ascii_case(name) {
            return Some(value);
        }
        rest = remaining.trim_start();
    }
    None
}

impl<T: EntryLike> Write for Context<'_, T> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.push_str(s);
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct UsageInfo {
    has_vars: bool,
    has_non_empty_vars: bool,
    has_used_macros: bool,
    has_non_empty_group: bool,
}

impl UsageInfo {
    /// Merge usage info with the info of a child.
    fn merge_child(self, child: Self) -> Self {
        Self {
            has_vars: self.has_vars || child.has_vars,
            has_non_empty_vars: self.has_non_empty_vars || child.has_non_empty_vars,
            has_used_macros: self.has_used_macros || child.has_used_macros,
            has_non_empty_group: self.has_non_empty_group || child.has_non_empty_group,
        }
    }

    /// Whether a group with this usage info should be rendered.
    fn should_render_group(&self) -> bool {
        !self.has_vars
            || (self.has_non_empty_vars
                || self.has_used_macros
                || self.has_non_empty_group)
    }
}

/// Describes the bracket preference of a citation style.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Brackets {
    /// "(...)" Parentheses.
    Round,
    /// "[...]" Brackets.
    Square,
    /// No brackets.
    None,
}

impl Brackets {
    /// Get the according left bracket.
    pub fn left(&self) -> Option<char> {
        match self {
            Brackets::Round => Some('('),
            Brackets::Square => Some('['),
            Brackets::None => None,
        }
    }

    /// Get the according right bracket.
    pub fn right(&self) -> Option<char> {
        match self {
            Brackets::Round => Some(')'),
            Brackets::Square => Some(']'),
            Brackets::None => None,
        }
    }
}

/// For what purpose to generate a citation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CitePurpose {
    /// The citation will only contain the name of the author.
    Author,
    /// The citation will only contain the year. Year Affixes will not be
    /// included.
    Year,
    /// The citation will equate to the bibliography entry of the item.
    Full,
    /// The citation will be well-suited for inclusion in prose.
    Prose,
    /// The regular citation is rendered with the author suppressed
    /// (citeproc-js `suppress-author`).
    SuppressAuthor,
}

/// A special citation form to use for the [`CitationItem`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum SpecialForm {
    /// Only output the author.
    VarOnly(Variable),
    /// Only print the first date.
    OnlyFirstDate,
    /// Only print the year suffix.
    OnlyYearSuffix,
    /// Output everything but the author.
    SuppressAuthor,
}

/// Recursively iterates over `child`. If we reach text, we return a mutable
/// reference to its content. If we reach an element with one child, we
/// recursively call the funtion with this child. Otherwise, we return [None].
fn get_last_text(child: &mut ElemChild) -> Option<&mut String> {
    match child {
        ElemChild::Text(formatted) => Some(&mut formatted.text),
        ElemChild::Elem(Elem { children, .. }) if children.0.len() == 1 => {
            get_last_text(&mut children.0[0])
        }
        _ => None,
    }
}

/// True iff the style uses the `year-suffix` variable in citations or bibliography. See #534.
fn uses_year_suffix_var(style: &StyleContext) -> bool {
    style
        .csl
        .citation
        .layout
        .elements
        .iter()
        .any(|e| has_year_suffix_var(e, style))
}

/// Collect the name variables rendered by the style's citations.
fn style_name_variables(csl: &IndependentStyle) -> Vec<NameVariable> {
    fn helper(
        e: &LayoutRenderingElement,
        style: &StyleContext,
        out: &mut Vec<NameVariable>,
    ) {
        use citationberg::TextTarget;
        match e {
            LayoutRenderingElement::Names(names) => {
                for variable in &names.variable {
                    if !out.contains(variable) {
                        out.push(*variable);
                    }
                }
            }
            LayoutRenderingElement::Text(Text {
                target: TextTarget::Macro { name },
                ..
            }) => {
                if let Some(mac) = style.get_macro(name) {
                    for child in &mac.children {
                        helper(child, style, out);
                    }
                }
            }
            LayoutRenderingElement::Group(Group { children, .. }) => {
                for child in children {
                    helper(child, style, out);
                }
            }
            LayoutRenderingElement::Choose(Choose { if_, else_if, otherwise }) => {
                for child in &if_.children {
                    helper(child, style, out);
                }
                for branch in else_if {
                    for child in &branch.children {
                        helper(child, style, out);
                    }
                }
                if let Some(otherwise) = otherwise {
                    for child in &otherwise.children {
                        helper(child, style, out);
                    }
                }
            }
            _ => {}
        }
    }

    let style = StyleContext::new(csl, None, &[]);
    let mut out = Vec::new();
    for element in &csl.citation.layout.elements {
        helper(element, &style, &mut out);
    }
    out
}

/// True iff the style renders the `citation-label` variable anywhere.
///
/// citeproc-js sets `has_year_suffix` when rendering a citation label, which
/// suppresses the implicit year suffix on `cs:date` (the label carries it).
fn uses_citation_label(style: &StyleContext) -> bool {
    style
        .csl
        .citation
        .layout
        .elements
        .iter()
        .any(|e| has_citation_label_var(e, style))
        || style.csl.bibliography.as_ref().is_some_and(|b| {
            b.layout.elements.iter().any(|e| has_citation_label_var(e, style))
        })
}

/// True iff the element `e` uses the `citation-label` variable.
fn has_citation_label_var(e: &LayoutRenderingElement, style: &StyleContext) -> bool {
    use citationberg::TextTarget;
    match e {
        LayoutRenderingElement::Text(Text {
            target:
                TextTarget::Variable {
                    var: Variable::Standard(StandardVariable::CitationLabel),
                    ..
                },
            ..
        }) => true,
        LayoutRenderingElement::Text(Text {
            target: TextTarget::Macro { name }, ..
        }) => style
            .get_macro(name)
            .map(|m| m.children.iter().any(|e| has_citation_label_var(e, style)))
            .unwrap_or(false),
        LayoutRenderingElement::Group(Group { children, .. }) => {
            children.iter().any(|e| has_citation_label_var(e, style))
        }
        LayoutRenderingElement::Choose(Choose { if_, else_if, otherwise }) => {
            if_.children.iter().any(|e| has_citation_label_var(e, style))
                || else_if.iter().any(|ei| {
                    ei.children.iter().any(|e| has_citation_label_var(e, style))
                })
                || otherwise.as_ref().is_some_and(|o| {
                    o.children.iter().any(|e| has_citation_label_var(e, style))
                })
        }
        _ => false,
    }
}

/// True iff the element `e` uses the `year-suffix` variable.
fn has_year_suffix_var(e: &LayoutRenderingElement, style: &StyleContext) -> bool {
    use citationberg::TextTarget;
    match e {
        LayoutRenderingElement::Text(Text {
            target:
                TextTarget::Variable {
                    var: Variable::Standard(StandardVariable::YearSuffix),
                    ..
                },
            ..
        }) => true,
        LayoutRenderingElement::Text(Text {
            target: TextTarget::Macro { name }, ..
        }) => style
            .get_macro(name)
            .map(|m| m.children.iter().any(|e| has_year_suffix_var(e, style)))
            .unwrap_or(false),
        LayoutRenderingElement::Group(Group { children, .. }) => {
            children.iter().any(|e| has_year_suffix_var(e, style))
        }
        LayoutRenderingElement::Choose(Choose { if_, else_if, otherwise }) => {
            if_.children.iter().any(|e| has_year_suffix_var(e, style))
                || else_if
                    .iter()
                    .any(|ei| ei.children.iter().any(|e| has_year_suffix_var(e, style)))
                || otherwise
                    .as_ref()
                    .map(|o| o.children.iter().any(|e| has_year_suffix_var(e, style)))
                    .unwrap_or(false)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use citationberg::LocaleFile;

    use super::*;
    use crate::{
        io::from_yaml_str,
        types::{Numeric, NumericValue},
    };

    #[test]
    fn test_csl() {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"));
        let en_locale =
            fs::read_to_string(workspace.join("tests/data/locales-en-US.xml")).unwrap();
        let en_locale = LocaleFile::from_xml(&en_locale).unwrap();

        let yaml = fs::read_to_string(workspace.join("tests/data/basic.yml")).unwrap();
        let bib = from_yaml_str(&yaml).unwrap();
        let en_locale = [en_locale.into()];

        for style_thing in fs::read_dir(workspace.join("styles/")).unwrap().take(100) {
            let thing = style_thing.unwrap();
            if thing.file_type().unwrap().is_dir() {
                continue;
            }

            let path = thing.path();
            let extension = path.extension();
            if let Some(extension) = extension {
                if extension.to_str() != Some("csl") {
                    continue;
                }
            } else {
                continue;
            }

            println!("testing {path:?}");
            let style = fs::read_to_string(path).unwrap();
            let style = IndependentStyle::from_xml(&style).unwrap();
            let mut driver = BibliographyDriver::new();

            for n in (0..bib.len()).step_by(2) {
                let items = vec![
                    CitationItem::with_entry(bib.nth(n).unwrap()),
                    CitationItem::with_entry(bib.nth(n + 1).unwrap()),
                ];
                driver.citation(CitationRequest::new(
                    items, &style, None, &en_locale, None,
                ));
            }

            driver.finish(BibliographyRequest {
                style: &style,
                locale: None,
                locale_files: &en_locale,
            });

            // for cite in finished.citations {
            //     println!("{}", cite.citation.to_string(BufWriteFormat::Plain))
            // }

            // if let Some(bib) = finished.bibliography {
            //     for (prefix, item) in bib.items {
            //         if let Some(prefix) = prefix {
            //             print!("{} ", prefix.to_string(BufWriteFormat::Plain))
            //         }
            //         println!("{}", item.to_string(BufWriteFormat::Html))
            //     }
            // }
        }
    }

    #[test]
    fn test_chapter_field() {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"));
        let yaml = fs::read_to_string(workspace.join("tests/data/basic.yml")).unwrap();
        let bib = from_yaml_str(&yaml).unwrap();
        let book = bib.get("lamb").unwrap();
        assert_eq!(book.chapter().unwrap(), &MaybeTyped::Typed(Numeric::new(20)));
        assert_eq!(book.volume().unwrap(), &MaybeTyped::Typed(Numeric::new(10)));
        assert_eq!(book.keyed_serial_number("serial"), None);
        assert_eq!(book.resolve_number_variable(NumberVariable::Number), None);

        let book = bib.get("snail").unwrap();
        assert_eq!(
            book.chapter().unwrap(),
            &MaybeTyped::Typed(Numeric {
                value: NumericValue::Number(2),
                prefix: None,
                suffix: Some(Box::new("A".into()))
            })
        );
        assert_eq!(
            book.volume().unwrap(),
            &MaybeTyped::Typed(Numeric {
                value: NumericValue::Number(4),
                prefix: None,
                suffix: Some(Box::new("B".into()))
            })
        );
        assert_eq!(book.keyed_serial_number("serial"), None);
        assert_eq!(book.resolve_number_variable(NumberVariable::Number), None);

        let chapter = bib.get("lamb-chapter").unwrap();
        assert_eq!(chapter.chapter().unwrap(), &MaybeTyped::Typed(Numeric::new(3)));
        assert_eq!(chapter.keyed_serial_number("serial"), None);
        assert_eq!(
            chapter.resolve_number_variable(NumberVariable::Number),
            Some(MaybeTyped::Typed(Cow::Borrowed(&Numeric::new(3))))
        );
        assert_eq!(chapter.volume(), None);
        assert_eq!(
            chapter.parents().first().unwrap().volume().unwrap(),
            &MaybeTyped::Typed(Numeric::new(10))
        );

        let chapter = bib.get("snail-chapter").unwrap();
        assert_eq!(chapter.chapter(), None);
        assert_eq!(chapter.keyed_serial_number("serial").unwrap(), "3");

        assert_eq!(chapter.volume(), None);
        assert_eq!(
            chapter.parents().first().unwrap().volume().unwrap(),
            &MaybeTyped::Typed(Numeric {
                value: NumericValue::Number(4),
                prefix: None,
                suffix: Some(Box::new("B".into()))
            })
        );
    }

    #[test]
    fn low_year_test() {
        let yield_year = |year, short| {
            let mut s = String::new();
            write_year(year, short, &mut s, "AD", "BC").unwrap();
            s
        };

        assert_eq!(yield_year(2021, false), "2021");
        assert_eq!(yield_year(2021, true), "21");
        assert_eq!(yield_year(0, false), "1BC");
        assert_eq!(yield_year(-1, false), "2BC");
        assert_eq!(yield_year(1, false), "1AD");
        assert_eq!(yield_year(0, true), "1BC");
        assert_eq!(yield_year(-1, true), "2BC");
        assert_eq!(yield_year(1, true), "1AD");
    }

    #[test]
    fn test_transparent_locator_ibid() {
        let test_data = r#"
            katalog:
                type: Book
                title: "Book"
                author: "Surname, Name"
                location: Warsaw
                date: 1971
            katalog2:
                type: Book
                title: "Book2"
                author: "Surname, Name"
                location: Warsaw
                date: 1971
        "#;
        let test_style = r#"<?xml version="1.0" encoding="utf-8"?>
        <style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0" demote-non-dropping-particle="sort-only">
           <info>
              <title>Citing style</title>
              <id>http://www.example.com/</id>
           </info>

           <citation>
              <layout prefix="" suffix="." delimiter="; ">
                 <choose>
                    <if position="first">
                      <text value="first" />
                    </if>
                    <else-if position="ibid-with-locator">
                      <text value="ibid-with-locator" />
                    </else-if>
                    <else-if position="ibid">
                       <text value="ibid" />
                    </else-if>
                    <else-if position="subsequent">
                      <text value="subsequent" />
                    </else-if>
                    <else>
                      <text value="other" />
                    </else>
                 </choose>
              </layout>
           </citation>
          <bibliography>
            <sort>
              <key macro="contributors-biblio"/>
            </sort>
            <layout suffix=".">
              <group delimiter=", ">
                <group delimiter=", ">
                  <text macro="locators-chapter"/>
                </group>
              </group>
            </layout>
          </bibliography>
        </style>"#;

        let library = from_yaml_str(test_data).unwrap();
        let style = citationberg::Style::from_xml(test_style).unwrap();
        let citationberg::Style::Independent(style) = style else { unreachable!() };

        let mut driver = BibliographyDriver::new();
        let citations = [
            ("katalog", Some([2, 3]), "first."),
            ("katalog", Some([2, 3]), "ibid."),
            ("katalog", Some([2, 3]), "ibid."),
            ("katalog", Some([2, 4]), "ibid-with-locator."),
            ("katalog", None, "subsequent."),
            ("katalog", Some([2, 3]), "ibid-with-locator."),
            ("katalog", Some([2, 3]), "ibid."),
            ("katalog2", Some([2, 3]), "first."),
        ];

        for (entry, supplement, _) in citations {
            let entry = library.get(entry).unwrap();
            driver.citation(CitationRequest::new(
                vec![CitationItem::with_locator(
                    entry,
                    supplement.map(|s| {
                        SpecificLocator(
                            Locator::Supplement,
                            LocatorPayload::Transparent(TransparentLocator(Arc::new(s))),
                        )
                    }),
                )],
                &style,
                None,
                &[],
                None,
            ));
        }

        let finished = driver.finish(BibliographyRequest {
            style: &style,
            locale: None,
            locale_files: &[],
        });

        for (citation, (_, _, expected_value)) in finished.citations.iter().zip(citations)
        {
            let mut s = String::new();
            citation.citation.write_buf(&mut s, BufWriteFormat::Plain).unwrap();
            assert_eq!(s, expected_value);
        }
    }

    #[test]
    #[cfg(feature = "archive")]
    fn test_alphanumeric_disambiguation() {
        let bibtex = r#"@article{chenTransMorphTransformerUnsupervised2021,
        title = {{{TransMorph}}: {{Transformer}} for Unsupervised Medical Image Registration},
        author = {Chen, Junyu and Frey, Eric C. and He, Yufan and Segars, William P. and Li, Ye and Du, Yong},
        date = {2021},
        }

        @article{chenViTVNetVisionTransformer2021,
        title = {{{ViT-V-Net}}: {{Vision Transformer}} for {{Unsupervised Volumetric Medical Image Registration}}},
        author = {Chen, Junyu and He, Yufan and Frey, Eric C. and Li, Ye and Du, Yong},
        date = {2021},
        }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let alphanumeric = archive::ArchivedStyle::Alphanumeric.get();
        let citationberg::Style::Independent(alphanumeric) = alphanumeric else {
            unreachable!()
        };

        let mut driver = BibliographyDriver::new();
        for entry in library.iter() {
            driver.citation(CitationRequest::new(
                vec![CitationItem::with_entry(entry)],
                &alphanumeric,
                None,
                &[],
                None,
            ));
        }

        let finished = driver.finish(BibliographyRequest {
            style: &alphanumeric,
            locale: None,
            locale_files: &[],
        });

        let mut c1 = String::new();
        let mut c2 = String::new();

        finished.citations[0]
            .citation
            .write_buf(&mut c1, BufWriteFormat::Plain)
            .unwrap();
        finished.citations[1]
            .citation
            .write_buf(&mut c2, BufWriteFormat::Plain)
            .unwrap();

        assert_eq!(c1, "[Che+21a]");
        assert_eq!(c2, "[Che+21b]");
    }

    #[test]
    #[cfg(feature = "archive")]
    fn issue_347() {
        let bibtex = r#"@book{pratchett96,
            title = {Eric},
            author = {Pratchett, T.},
            year = {1996},
            publisher = {Vista}
        }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let mla = archive::ArchivedStyle::ModernLanguageAssociation.get();
        let citationberg::Style::Independent(mla) = mla else { unreachable!() };
        let entry = library.iter().next().unwrap();
        let locales = archive::locales();

        let mut driver = BibliographyDriver::new();
        driver.citation(CitationRequest::new(
            vec![CitationItem::with_entry(entry).kind(CitePurpose::Prose)],
            &mla,
            None,
            &locales,
            None,
        ));
        let rendered = driver.finish(BibliographyRequest::new(&mla, None, &locales));
        let mut output = String::new();
        rendered.citations[0]
            .citation
            .write_buf(&mut output, BufWriteFormat::Plain)
            .unwrap();

        assert_eq!(output, "Pratchett");
    }

    #[test]
    #[cfg(feature = "archive")]
    /// See https://github.com/typst/hayagriva/issues/470
    fn issue_470() {
        let bibtex = r#"@article{alpha,
            author = {Smith, Alice and Brown, Chris and Davis, Emily},
            title = {Alpha},
            journaltitle = {Journal of Examples},
            date = {2020},
            volume = {1},
            pages = {1--10}
        }

        @article{beta,
            author = {Smith, Bob and Evans, Frank and Green, Grace},
            title = {Beta},
            journaltitle = {Journal of Examples},
            date = {2020},
            volume = {2},
            pages = {11--20}
        }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let apa = archive::ArchivedStyle::AmericanPsychologicalAssociation.get();
        let citationberg::Style::Independent(apa) = apa else { unreachable!() };
        let locales = archive::locales();

        let mut driver = BibliographyDriver::new();
        for key in ["alpha", "beta"] {
            driver.citation(CitationRequest::new(
                vec![CitationItem::with_entry(library.get(key).unwrap())],
                &apa,
                None,
                &locales,
                None,
            ));
        }

        let rendered = driver.finish(BibliographyRequest::new(&apa, None, &locales));

        let mut cites = Vec::new();
        for citation in &rendered.citations {
            let mut buf = String::new();
            citation.citation.write_buf(&mut buf, BufWriteFormat::Plain).unwrap();
            cites.push(buf);
        }

        // Cites of ambiguous entries must be disambiguated with initials.
        assert_eq!(cites[0], "(A. Smith et al., 2020)");
        assert_eq!(cites[1], "(B. Smith et al., 2020)");

        let bib = &rendered.bibliography.as_ref().unwrap().items;
        let mut output = String::new();
        for item in bib {
            item.content.write_buf(&mut output, BufWriteFormat::Plain).unwrap();
            output.push('\n');
        }

        // The bibliography must keep the full author lists.
        assert_eq!(
            output,
            "Smith, A., Brown, C., & Davis, E. (2020). Alpha. Journal of Examples, 1, 1–10.\n\
             Smith, B., Evans, F., & Green, G. (2020). Beta. Journal of Examples, 2, 11–20.\n"
        );
    }

    #[test]
    #[cfg(feature = "archive")]
    /// See https://github.com/typst/hayagriva/issues/243
    fn issue_243() {
        let bibtex = r#"@book{downs57,
            title = {An Economic Theory of Democracy},
            author = {Downs, Anthony},
            date = {1957},
            edition = {1},
            publisher = {Harper \& Row},
            location = {New York},
            langid = {english}
            }

            @book{brady_collier10,
            title = {Rethinking Social Inquiry. Diverse Tools, Shared Standards},
            editor = {Brady, Henry E. and Collier, David},
            date = {2010},
            edition = {2},
            publisher = {Rowman \& Littlefield Publishers},
            location = {Maryland}
            }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let apa = archive::ArchivedStyle::AmericanPsychologicalAssociation.get();
        let citationberg::Style::Independent(apa) = apa else { unreachable!() };

        let locales = archive::locales();

        let mut driver = BibliographyDriver::new();
        for entry in library.iter() {
            driver.citation(CitationRequest::new(
                vec![CitationItem::new(
                    entry,
                    None,
                    Some(LocaleCode::en_us()),
                    false,
                    Some(CitePurpose::Prose),
                )],
                &apa,
                Some(LocaleCode::en_us()),
                &locales,
                None,
            ));
        }

        let finished = driver.finish(BibliographyRequest {
            style: &apa,
            locale: Some(LocaleCode::en_us()),
            locale_files: &locales,
        });

        let mut c1 = String::new();
        let mut c2 = String::new();

        finished.citations[0]
            .citation
            .write_buf(&mut c1, BufWriteFormat::Plain)
            .unwrap();
        finished.citations[1]
            .citation
            .write_buf(&mut c2, BufWriteFormat::Plain)
            .unwrap();

        assert_eq!(c1, "Downs (1957)");
        assert_eq!(c2, "Brady & Collier (2010)");
    }

    #[test]
    fn input_rich_text_markup() {
        // citeproc-js parses a small HTML subset in CSL-JSON strings:
        // formatting tags become runs, `nocase` content bypasses text-case,
        // and the tags never reach the output.
        let style = citationberg::Style::from_xml(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0">
                 <info><id/><title/><updated>2009-08-10T04:49:00+09:00</updated></info>
                 <citation>
                   <layout><text variable="title" text-case="title" quotes="true"/></layout>
                 </citation>
               </style>"#,
        )
        .unwrap();
        let citationberg::Style::Independent(style) = style else { unreachable!() };

        let library = crate::io::from_yaml_str(
            r#"a:
                 type: Book
                 title: a <i>smith</i> <b>pencil</b> <span class="nocase">SMITH</span>
            "#,
        )
        .unwrap();
        let entry = library.get("a").unwrap();

        let mut driver = BibliographyDriver::new();
        driver.citation(CitationRequest::new(
            vec![CitationItem::with_entry(entry)],
            &style,
            None,
            &[],
            None,
        ));
        let rendered = driver.finish(BibliographyRequest {
            style: &style,
            locale: None,
            locale_files: &[],
        });
        let mut output = String::new();
        rendered.citations[0]
            .citation
            .write_buf(&mut output, BufWriteFormat::Plain)
            .unwrap();
        // No locale files are loaded, so quotes fall back to straight quotes.
        assert_eq!(output, "\"A Smith Pencil SMITH\"");
    }

    #[test]
    #[cfg(feature = "archive")]
    /// See https://github.com/typst/hayagriva/issues/530
    fn issue_530() {
        let bibtex = r#"@misc{a1,
                title={One},
                author={{Same Org}}
            }

            @misc{a2,
                title={Two},
                author={{Same Org}}
            }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let a1 = library.get("a1").unwrap();
        let a2 = library.get("a2").unwrap();
        let apa = archive::ArchivedStyle::AmericanPsychologicalAssociation.get();
        let citationberg::Style::Independent(apa) = apa else { unreachable!() };

        let locales = archive::locales();

        let mut driver = BibliographyDriver::new();

        driver.citation(CitationRequest::new(
            vec![CitationItem::new(a1, None, Some(LocaleCode::en_us()), false, None)],
            &apa,
            Some(LocaleCode::en_us()),
            &locales,
            None,
        ));
        driver.citation(CitationRequest::new(
            vec![CitationItem::new(a2, None, Some(LocaleCode::en_us()), false, None)],
            &apa,
            Some(LocaleCode::en_us()),
            &locales,
            None,
        ));
        driver.citation(CitationRequest::new(
            vec![
                CitationItem::new(a1, None, Some(LocaleCode::en_us()), false, None),
                CitationItem::new(a2, None, Some(LocaleCode::en_us()), false, None),
            ],
            &apa,
            Some(LocaleCode::en_us()),
            &locales,
            None,
        ));

        let finished = driver.finish(BibliographyRequest {
            style: &apa,
            locale: Some(LocaleCode::en_us()),
            locale_files: &locales,
        });

        let mut c1 = String::new();
        let mut c2 = String::new();
        let mut c3 = String::new();

        finished.citations[0]
            .citation
            .write_buf(&mut c1, BufWriteFormat::Plain)
            .unwrap();
        finished.citations[1]
            .citation
            .write_buf(&mut c2, BufWriteFormat::Plain)
            .unwrap();
        finished.citations[2]
            .citation
            .write_buf(&mut c3, BufWriteFormat::Plain)
            .unwrap();

        assert_eq!(c1, "(Same Org, n.d.-a)");
        assert_eq!(c2, "(Same Org, n.d.-b)");
        assert_eq!(c3, "(Same Org, n.d.-a, n.d.-b)");
    }

    #[test]
    #[cfg(feature = "archive")]
    /// A webpage with only a year (no month/day) as its issued date must not render a dangling delimiter before the (empty) month/day part.
    ///
    /// See https://github.com/typst/hayagriva/issues/246
    fn issue_year_only_date_apa() {
        let yaml = r#"
        nistCVE:
            type: Web
            author: "NIST"
            title: "CVE-2021-44228"
            date: "2021"
            url:
                value: "https://nvd.nist.gov/vuln/detail/CVE-2021-44228"
                date: 2024-10-28
        "#;

        let library = from_yaml_str(yaml).unwrap();
        let apa = archive::ArchivedStyle::AmericanPsychologicalAssociation.get();
        let citationberg::Style::Independent(apa) = apa else { unreachable!() };
        let locales = archive::locales();

        let mut driver = BibliographyDriver::new();
        driver.citation(CitationRequest::new(
            vec![CitationItem::with_entry(library.iter().next().unwrap())],
            &apa,
            None,
            &locales,
            None,
        ));

        let finished = driver.finish(BibliographyRequest {
            style: &apa,
            locale: None,
            locale_files: &locales,
        });

        let mut bib_entry = String::new();
        finished
            .bibliography
            .unwrap()
            .items
            .remove(0)
            .content
            .write_buf(&mut bib_entry, BufWriteFormat::Plain)
            .unwrap();

        assert_eq!(
            bib_entry,
            "NIST. (2021). CVE-2021-44228. https://nvd.nist.gov/vuln/detail/CVE-2021-44228"
        );
    }

    #[test]
    #[cfg(feature = "archive")]
    /// See https://github.com/typst/hayagriva/issues/48
    fn issue_48() {
        let bibtex = r#"@article{chenTransMorphTransformerUnsupervised2021,
        title = {{{TransMorph}}: {{Transformer}} for Unsupervised Medical Image Registration},
        author = {Chen, Junyu and Frey, Eric C. and He, Yufan and Segars, William P. and Li, Ye and Du, Yong},
        date = {2021},
        }

        @article{chenViTVNetVisionTransformer2021,
        title = {{{ViT-V-Net}}: {{Vision Transformer}} for {{Unsupervised Volumetric Medical Image Registration}}},
        author = {Chen, Junyu and He, Yufan and Frey, Eric C. and Li, Ye and Du, Yong},
        date = {2021},
        }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let alphanumeric = archive::ArchivedStyle::Alphanumeric.get();
        let citationberg::Style::Independent(alphanumeric) = alphanumeric else {
            unreachable!()
        };

        let mut driver = BibliographyDriver::new();

        let locator = SpecificLocator(Locator::Custom, LocatorPayload::Str("12"));
        for entry in library.iter() {
            driver.citation(CitationRequest::new(
                vec![CitationItem::with_locator(entry, Some(locator.clone()))],
                &alphanumeric,
                None,
                &[],
                None,
            ));
        }

        driver.citation(CitationRequest::new(
            vec![CitationItem::with_locator(library.iter().next().unwrap(), None)],
            &alphanumeric,
            None,
            &[],
            None,
        ));

        let finished = driver.finish(BibliographyRequest {
            style: &alphanumeric,
            locale: None,
            locale_files: &[],
        });

        let mut c1 = String::new();
        let mut c2 = String::new();
        let mut c3 = String::new();

        finished.citations[0]
            .citation
            .write_buf(&mut c1, BufWriteFormat::Plain)
            .unwrap();
        finished.citations[1]
            .citation
            .write_buf(&mut c2, BufWriteFormat::Plain)
            .unwrap();
        finished.citations[2]
            .citation
            .write_buf(&mut c3, BufWriteFormat::Plain)
            .unwrap();

        assert_eq!(c1, "[Che+21a, 12]");
        assert_eq!(c2, "[Che+21b, 12]");
        assert_eq!(c3, "[Che+21a]");
    }

    #[test]
    #[cfg(feature = "archive")]
    fn ibid_handling_with_deutsche_sprache_csl() {
        let bibtex = r#"@book{ITEM,
            title = {A},
            type = {book},
            }"#;

        let library = crate::io::from_biblatex_str(bibtex).unwrap();
        let style = archive::ArchivedStyle::DeutscheSprache.get();
        let citationberg::Style::Independent(style) = style else { unreachable!() };

        let mut driver = BibliographyDriver::new();
        let entry = library.iter().next().unwrap();

        for locator in ["33", "33", "34"] {
            driver.citation(CitationRequest::new(
                vec![CitationItem::new(
                    entry,
                    Some(SpecificLocator(Locator::Page, LocatorPayload::Str(locator))),
                    None,
                    false,
                    Some(CitePurpose::Prose),
                )],
                &style,
                None,
                &[],
                None,
            ));
        }

        let finished = driver.finish(BibliographyRequest {
            style: &style,
            locale: None,
            locale_files: &[],
        });

        let actual = finished
            .citations
            .iter()
            .map(|c| {
                let mut s = String::new();
                c.citation.write_buf(&mut s, BufWriteFormat::Plain).unwrap();
                s
            })
            .collect::<Vec<_>>();

        assert_eq!(actual, ["(33)", "()", "(34)"]);
    }

    /// Render a single citation with `style` as plain text.
    fn render_citation<T: EntryLike + Hash + PartialEq + Eq + Debug>(
        style: &IndependentStyle,
        items: Vec<CitationItem<'_, T>>,
    ) -> String {
        let mut driver = BibliographyDriver::new();
        driver.citation(CitationRequest::new(items, style, None, &[], Some(1)));
        let finished = driver.finish(BibliographyRequest::new(style, None, &[]));
        let mut s = String::new();
        finished.citations[0]
            .citation
            .write_buf(&mut s, BufWriteFormat::Plain)
            .unwrap();
        s
    }

    #[test]
    fn affix_prefix_in_layout_affixes() {
        // Derived from the `affix_PrefixFullCitationTextOnly` test-suite
        // fixture. The item prefix is inserted inside the layout's affixes.
        let style = IndependentStyle::from_xml(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0">
              <info>
                <id>affix-test</id>
                <title>Affix Test</title>
                <updated>2007-10-26T21:32:52+02:00</updated>
              </info>
              <citation>
                <layout prefix="(" suffix=")">
                  <group delimiter=" ">
                    <names variable="author"><name form="short"/></names>
                    <date variable="issued"><date-part name="year"/></date>
                  </group>
                </layout>
              </citation>
            </style>"#,
        )
        .unwrap();

        let library = from_yaml_str(
            r#"
            smith:
                type: Book
                title: Book C
                author: "Smith, John"
                date: 2000
            "#,
        )
        .unwrap();

        let citation = render_citation(
            &style,
            vec![
                CitationItem::with_entry(library.get("smith").unwrap())
                    .with_affixes(Some("As written in ".to_string()), None),
            ],
        );

        assert_eq!(citation, "(As written in Smith 2000)");
    }

    #[test]
    fn affix_prefix_with_comma() {
        // Derived from the `affix_CommaAfterQuote` test-suite fixture. This
        // render is locale-less (`locale_files: &[]`), so there are no
        // `open-quote`/`close-quote` terms to substitute and the quotation
        // marks stay straight. The locale-aware behavior is covered by the
        // `quotes_AffixCommaAfterQuote` citeproc fixture.
        let style = IndependentStyle::from_xml(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0">
              <info>
                <id>affix-test</id>
                <title>Affix Test</title>
                <updated>2009-08-10T04:49:00+09:00</updated>
              </info>
              <citation>
                <layout><text variable="title"/></layout>
              </citation>
            </style>"#,
        )
        .unwrap();

        let library = from_yaml_str(
            r#"
            item:
                type: Book
                title: Hello Thing
            "#,
        )
        .unwrap();

        let citation = render_citation(
            &style,
            vec![
                CitationItem::with_entry(library.get("item").unwrap())
                    .with_affixes(Some("'quote', ".to_string()), None),
            ],
        );

        assert_eq!(citation, "\"quote\", Hello Thing");
    }

    #[test]
    fn affix_suffix() {
        // The suffix is literal and rendered directly after the item's
        // content. Cf. the second line of the
        // `affix_WordProcessorAffixNoSpace` fixture.
        let style = IndependentStyle::from_xml(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0">
              <info>
                <id>affix-test</id>
                <title>Affix Test</title>
                <updated>2009-08-10T04:49:00+09:00</updated>
              </info>
              <citation>
                <layout><text variable="title"/></layout>
              </citation>
            </style>"#,
        )
        .unwrap();

        let library = from_yaml_str(
            r#"
            item:
                type: Book
                title: My Title
            "#,
        )
        .unwrap();

        let citation = render_citation(
            &style,
            vec![
                CitationItem::with_entry(library.get("item").unwrap())
                    .with_affixes(None, Some(", My Suffix".to_string())),
            ],
        );

        assert_eq!(citation, "My Title, My Suffix");
    }

    #[test]
    fn affix_prefix_and_suffix_on_multi_item_citation() {
        // Both affixes are placed inside the layout's inter-item delimiter.
        // The prefix and suffix are the second line of the
        // `affix_WordProcessorAffixNoSpace` fixture.
        let style = IndependentStyle::from_xml(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0">
              <info>
                <id>affix-test</id>
                <title>Affix Test</title>
                <updated>2009-08-10T04:49:00+09:00</updated>
              </info>
              <citation>
                <layout delimiter="; "><text variable="title"/></layout>
              </citation>
            </style>"#,
        )
        .unwrap();

        let library = from_yaml_str(
            r#"
            item:
                type: Book
                title: My Title
            other:
                type: Book
                title: Book Two
            "#,
        )
        .unwrap();

        let citation = render_citation(
            &style,
            vec![
                CitationItem::with_entry(library.get("item").unwrap()).with_affixes(
                    Some("My Prefix. ".to_string()),
                    Some(", My Suffix".to_string()),
                ),
                CitationItem::with_entry(library.get("other").unwrap()),
            ],
        );

        assert_eq!(citation, "My Prefix. My Title, My Suffix; Book Two");
    }

    #[test]
    fn affix_prefix_comma_suppresses_delimiter() {
        // Exact expected output of the
        // `magic_SuppressLayoutDelimiterIfPrefixComma` test-suite fixture: a
        // prefix starting with a comma suppresses the layout delimiter.
        let style = IndependentStyle::from_xml(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="note" version="1.0">
              <info>
                <id>affix-test</id>
                <title>Affix Test</title>
                <updated>2009-08-10T04:49:00+09:00</updated>
              </info>
              <citation>
                <layout delimiter="; "><text variable="title"/></layout>
              </citation>
            </style>"#,
        )
        .unwrap();

        let library = from_yaml_str(
            r#"
            item:
                type: Book
                title: Book A
            other:
                type: Book
                title: Book B
            "#,
        )
        .unwrap();

        let citation = render_citation(
            &style,
            vec![
                CitationItem::with_entry(library.get("item").unwrap()),
                CitationItem::with_entry(library.get("other").unwrap())
                    .with_affixes(Some(", cited in ".to_string()), None),
            ],
        );

        assert_eq!(citation, "Book A, cited in Book B");
    }

    #[cfg(feature = "csl-json")]
    #[test]
    fn csl_json_date_conversion() {
        // CSL-JSON numbers years historically (-250 is 250 BCE) while the
        // internal representation uses 0 for 1 BCE.
        let item: citationberg::json::Item =
            serde_json::from_str(r#"{"id":"a","issued":{"date-parts":[[-250,13,1]]}}"#)
                .unwrap();
        let date = item.resolve_date_variable(DateVariable::Issued).expect("date");
        assert_eq!(date.year, -249);
        let mut year = String::new();
        write_year(date.year, false, &mut year, " AD", " BC").unwrap();
        assert_eq!(year, "250 BC");
        // Month 13 is the CSL spring season, not a month.
        assert_eq!(date.month, None);
        assert_eq!(date.season, Some(citationberg::taxonomy::Season::Spring));

        // Literal dates are exposed separately from machine-readable parts.
        let item: citationberg::json::Item = serde_json::from_str(
            r#"{"id":"b","issued":{"date-parts":[],"literal":"(in press)"}}"#,
        )
        .unwrap();
        assert!(item.resolve_date_variable(DateVariable::Issued).is_none());
        assert_eq!(
            item.resolve_date_literal(DateVariable::Issued).as_deref(),
            Some("(in press)")
        );
    }

    #[cfg(feature = "csl-json")]
    #[test]
    fn csl_json_citation_label_trigraph() {
        let item: citationberg::json::Item = serde_json::from_str(
            r#"{"id":"a","author":[{"family":"Aalto","given":"Alan"}],"issued":{"date-parts":[[2002]]}}"#,
        )
        .unwrap();
        let label = item
            .resolve_standard_variable(
                LongShortForm::Long,
                StandardVariable::CitationLabel,
            )
            .expect("label")
            .to_string();
        assert_eq!(label, "Aalt02");
    }

    #[test]
    fn name_registry_counts() {
        let mut registry = NameRegistry::default();
        let person = |family: &str, given: &str| Person {
            name: family.to_string(),
            given_name: Some(given.to_string()),
            prefix: None,
            suffix: None,
            alias: None,
            comma_suffix: false,
            literal_family: false,
            non_dropping_particle: None,
        };
        registry.register(&person("Oblinger", "Dan Gerry"));
        registry.register(&person("Oblinger", "Susan Mary"));
        assert_eq!(registry.counts(&person("Oblinger", "Dan Gerry")), (2, 1));
        // Initials are compared without periods or spacing
        // (`disambiguate_DifferentSpacingInInitials`).
        registry.register(&person("Doe", "J. J."));
        registry.register(&person("Doe", "J.J."));
        assert_eq!(registry.counts(&person("Doe", "J. J.")), (1, 1));
    }
}
