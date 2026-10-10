use std::borrow::Cow;
use std::fmt::Write;
use std::str::FromStr;

use citationberg::taxonomy::{
    Locator, NumberOrPageVariable, NumberVariable, OtherTerm, PageVariable,
    StandardVariable, Term, Variable,
};
use citationberg::{
    ChooseBranch, CslMacro, DateDayForm, DateMonthForm, DatePartName, DateParts,
    DateStrongAnyForm, GrammarGender, LabelPluralize, LayoutRenderingElement,
    LongShortForm, NumberForm, PageRangeFormat, TestPosition, TextCase, ToAffixes,
    ToFormatting,
};
use citationberg::{TermForm, TextTarget};

use crate::PageRanges;
use crate::csl::Sorting;
use crate::csl::taxonomy::{NumberVariableResult, PageVariableResult};
use crate::lang::{Case, SentenceCase, TitleCase};
use crate::types::{ChunkedString, Date, MaybeTyped, Numeric};

use super::taxonomy::{EntryLike, NumberOrPageVariableResult};
use super::{
    Context, ElemMeta, IbidState, SpecialForm, UsageInfo, capitalize_first, write_year,
};

pub mod names;

/// All rendering elements implement this trait. It allows you to format an
/// [`Entry`] with them.
pub(crate) trait RenderCsl {
    /// Render the element given the context's Entry into the context's buffer.
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>);
    /// Check whether the element will render a given variable.
    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool;
    /// Check whether the element will print something and what.
    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo);
}

impl RenderCsl for citationberg::Text {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        let Some(target) = ResolvedTextTarget::compute(self, ctx) else { return };
        // Whether this is the first thing rendered in the current item,
        // before the element's own affixes are applied.
        let nothing_rendered = ctx.writing.len() == 0;
        // The formatting inherited from the element's ancestors; affixes are
        // decorated by it but not by the element's own formatting (F-116).
        let ambient = *ctx.writing.formatting();
        // While rendering bibliography entries, citeproc-js opens the
        // formatting scope of a text element around its value only: affixes
        // and quote marks stay outside and inherit the enclosing formatting.
        // The value is rendered in its own scope element so that serializers
        // can reproduce the tags.
        let scoped = ctx.bibliography && !self.formatting.is_empty();
        let depth = ctx.push_elem(if scoped {
            citationberg::Formatting::default()
        } else {
            self.formatting
        });

        // Only print affixes if this macro is not used out of its original context.
        #[allow(clippy::match_like_matches_macro)]
        let print_affixes = match ctx.instance.kind {
            Some(SpecialForm::VarOnly(_))
                if matches!(&self.target, TextTarget::Macro { .. }) =>
            {
                false
            }
            _ => true,
        };

        /// Gets the url prefix for a given StandardVariable if one exists.
        ///
        /// These are those prefixes in the Appendix IV of the CSL 1.0.2 spec.
        fn get_url_prefix(var: StandardVariable) -> Option<&'static str> {
            match var {
                StandardVariable::DOI => Some("https://doi.org/"),
                StandardVariable::PMID => Some("https://www.ncbi.nlm.nih.gov/pubmed/"),
                StandardVariable::PMCID => {
                    Some("https://www.ncbi.nlm.nih.gov/pmc/articles/")
                }
                _ => None,
            }
        }

        // Check if a URL prefix exists for the target and if so, if the CSL specifies
        // the URL prefix as the affix. If this is the case, we want to make sure the
        // URL prefix is a part of the link (and therefore not printed here, but later).
        let affix_is_url_prefix = match &target {
            ResolvedTextTarget::StandardVariable(var, _) => get_url_prefix(*var)
                .is_some_and(|prefix| self.affixes.prefix.as_deref() == Some(prefix)),
            _ => false,
        };

        let affix_loc = (print_affixes && !affix_is_url_prefix)
            .then(|| ctx.apply_prefix(&self.affixes, ambient));

        if self.quotes {
            ctx.push_quotes();
        }

        let scope_depth = scoped.then(|| ctx.push_scoped_elem(self.formatting));

        ctx.may_strip_periods(self.strip_periods);
        let cidx = ctx.push_case(self.text_case);

        let mut should_render = true;

        match target {
            ResolvedTextTarget::StandardVariable(var, val) => {
                if let Some(url_prefix) = get_url_prefix(var) {
                    // For link variables, create the full URL for the destination of the link.
                    let full_url = format!("{}{}", url_prefix, val);

                    let (display, destination) = if affix_is_url_prefix {
                        // If the affix in the CSL was the URL prefix, then use
                        // the full URL as both the link displayed and its destination.
                        (full_url.clone(), full_url)
                    } else {
                        // Otherwise, display the value (e.g. the DOI) with the full URL
                        // as its destination.
                        (val.to_string(), full_url)
                    };

                    ctx.push_link(&display.into(), destination);
                } else if var == StandardVariable::URL {
                    ctx.push_link(&val, val.to_string());
                } else {
                    ctx.push_chunked(&val);
                }
            }
            ResolvedTextTarget::NumberVariable(_, n) => match n {
                NumberVariableResult::Regular(MaybeTyped::Typed(num))
                    if num.will_transform() =>
                {
                    render_typed_num(num.as_ref(), NumberForm::default(), None, ctx);
                }
                NumberVariableResult::Regular(n) => ctx.push_str(&n.to_str()),
                NumberVariableResult::Transparent(n) => ctx.push_transparent(n),
            },
            ResolvedTextTarget::PageVariable(p) => match p {
                MaybeTyped::Typed(r) => render_page_range(&r, ctx),
                MaybeTyped::String(s) => ctx.push_str(&s.replace('-', "–")),
            },
            ResolvedTextTarget::Macro(mac) => {
                // Treat macros as groups: don't render if all variables are empty.
                let info = self.will_have_info(ctx).1;
                should_render = info.should_render_group();
                if should_render {
                    // Delimiters from ancestor delimiting elements are NOT
                    // applied within.
                    let idx = ctx.writing.push_delimiter(None);
                    for child in &mac.children {
                        child.render(ctx);
                    }
                    ctx.writing.pop_delimiter(idx);
                }
            }
            ResolvedTextTarget::Term(s) => {
                if nothing_rendered && ctx.should_capitalize_term() {
                    ctx.push_str(&capitalize_first(s));
                } else {
                    ctx.push_str(s);
                }
            }
            ResolvedTextTarget::Value(val) => ctx.push_str(val),
        }

        ctx.pop_case(cidx);
        ctx.stop_stripping_periods();

        if let Some(scope_depth) = scope_depth {
            ctx.commit_elem(scope_depth, None, None);
        }

        if self.quotes {
            ctx.pop_quotes();
            ctx.may_pull_punctuation();
        }

        if let Some(affix_loc) = affix_loc {
            ctx.apply_suffix(&self.affixes, affix_loc, ambient);
        }
        if should_render {
            ctx.commit_elem(
                depth,
                self.display,
                match self.target {
                    TextTarget::Variable { var, .. }
                        if var == NumberVariable::CitationNumber.into() =>
                    {
                        Some(ElemMeta::CitationNumber)
                    }
                    TextTarget::Variable { var, .. }
                        if var == StandardVariable::CitationLabel.into() =>
                    {
                        Some(ElemMeta::CitationLabel)
                    }
                    TextTarget::Variable { .. } => Some(ElemMeta::Text),
                    _ => None,
                },
            );
        } else {
            ctx.discard_elem(depth);
        }
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        let Some(target) = ResolvedTextTarget::compute(self, ctx) else {
            return false;
        };
        match target {
            ResolvedTextTarget::StandardVariable(s, _) => var == Variable::Standard(s),
            ResolvedTextTarget::NumberVariable(n, _) => var == Variable::Number(n),
            ResolvedTextTarget::PageVariable(_) => {
                var == Variable::Page(PageVariable::Page)
            }
            ResolvedTextTarget::Macro(mac) => {
                mac.children.iter().any(|c| c.will_render(ctx, var))
            }
            ResolvedTextTarget::Term(_) => false,
            ResolvedTextTarget::Value(_) => false,
        }
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        // If suppress_queried_variables is set to true, we need to perform a
        // silent lookup, otherwise we need to perform a regular lookup.
        let suppressing = ctx.writing.suppress_queried_variables;

        ctx.writing.stop_suppressing_queried_variables();
        let lookup_result = ResolvedTextTarget::compute(self, ctx);
        if suppressing {
            ctx.writing.start_suppressing_queried_variables();
        }
        let targets_variable = match self.target {
            // Year suffix is not counted as a variable
            TextTarget::Variable {
                var: Variable::Standard(StandardVariable::YearSuffix),
                ..
            } => false,
            TextTarget::Variable { .. } => true,
            _ => false,
        };

        let Some(target) = lookup_result else {
            return (
                false,
                UsageInfo { has_vars: targets_variable, ..Default::default() },
            );
        };

        match target {
            ResolvedTextTarget::StandardVariable(_, s) if s.is_empty() => {
                (false, UsageInfo { has_vars: true, ..Default::default() })
            }
            ResolvedTextTarget::StandardVariable(_, _)
            | ResolvedTextTarget::NumberVariable(_, _)
            | ResolvedTextTarget::PageVariable(_) => (
                true,
                UsageInfo {
                    has_vars: true,
                    has_non_empty_vars: true,
                    ..Default::default()
                },
            ),
            ResolvedTextTarget::Macro(mac) => {
                let mut will_print = false;
                let mut info = UsageInfo::default();
                for child in &mac.children {
                    let (print, child_info) = child.will_have_info(ctx);
                    will_print |= print;
                    info = info.merge_child(child_info)
                }

                // Treat macro as group: don't render if all variables are
                // empty.
                will_print &= info.should_render_group();

                (will_print, UsageInfo { has_used_macros: will_print, ..info })
            }
            ResolvedTextTarget::Term(_) => (true, UsageInfo::default()),
            ResolvedTextTarget::Value(v) => (!v.is_empty(), UsageInfo::default()),
        }
    }
}

#[derive(Debug)]
enum ResolvedTextTarget<'a, 'b> {
    StandardVariable(StandardVariable, Cow<'a, ChunkedString>),
    NumberVariable(NumberVariable, NumberVariableResult<'a>),
    PageVariable(PageVariableResult),
    Macro(&'a CslMacro),
    Term(&'a str),
    Value(&'b str),
}

impl<'a, 'b> ResolvedTextTarget<'a, 'b> {
    fn compute<T: EntryLike>(
        text: &'b citationberg::Text,
        ctx: &mut Context<'a, T>,
    ) -> Option<Self> {
        match ctx.instance.kind {
            // If we are supposed to print a variable we need to return if this
            // is neither a macro nor that variable.
            Some(SpecialForm::VarOnly(v))
                if !matches!(&text.target, TextTarget::Macro { .. }) =>
            {
                match text.target {
                    TextTarget::Variable { var, .. } if var == v => {}
                    _ => return None,
                }
            }
            // Also render the `no-date` term when applying suffixes.
            Some(SpecialForm::OnlyFirstDate)
                if !matches!(&text.target, TextTarget::Macro { .. })
                    && !matches!(
                        text.target,
                        TextTarget::Variable {
                            var: Variable::Standard(StandardVariable::YearSuffix)
                                | Variable::Number(NumberVariable::Locator),
                            ..
                        } | TextTarget::Term { term: Term::Other(OtherTerm::NoDate), .. },
                    ) =>
            {
                return None;
            }
            Some(SpecialForm::OnlyYearSuffix)
                if !matches!(&text.target, TextTarget::Macro { .. })
                    && !matches!(
                        text.target,
                        TextTarget::Variable {
                            var: Variable::Standard(StandardVariable::YearSuffix)
                                | Variable::Number(NumberVariable::Locator),
                            ..
                        }
                    ) =>
            {
                return None;
            }
            _ => {}
        }

        match &text.target {
            TextTarget::Variable { var: Variable::Standard(var), form } => ctx
                .resolve_standard_variable(*form, *var)
                .map(|s| ResolvedTextTarget::StandardVariable(*var, s)),
            TextTarget::Variable { var: Variable::Number(var), .. } => ctx
                .resolve_number_variable(*var)
                .map(|n| ResolvedTextTarget::NumberVariable(*var, n)),
            TextTarget::Variable { var: Variable::Page(pv), .. } => {
                ctx.resolve_page_variable(*pv).map(ResolvedTextTarget::PageVariable)
            }
            TextTarget::Variable { .. } => None,
            TextTarget::Macro { name } => {
                ctx.style.get_macro(name).map(ResolvedTextTarget::Macro)
            }
            TextTarget::Term { term, form, plural } => {
                ctx.term(*term, *form, *plural).map(ResolvedTextTarget::Term)
            }
            TextTarget::Value { val } => Some(ResolvedTextTarget::Value(val)),
        }
    }
}

impl RenderCsl for citationberg::Number {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        if !self.will_render(ctx, self.variable.into()) {
            return;
        }

        let value = ctx.resolve_number_or_page_variable(self.variable);
        if ctx.instance.sorting.is_some() {
            match value {
                Some(NumberOrPageVariableResult::Number(
                    NumberVariableResult::Regular(MaybeTyped::Typed(n)),
                )) => {
                    n.fmt_value(ctx, true).unwrap();
                    return;
                }
                Some(NumberOrPageVariableResult::Page(MaybeTyped::Typed(p))) => {
                    write!(ctx, "{p}").unwrap();
                    return;
                }
                _ => {}
            }
        }

        let ambient = *ctx.writing.formatting();
        let depth = ctx.push_elem(self.formatting);
        let affix_loc = ctx.apply_prefix(&self.affixes, ambient);
        let cidx = ctx.push_case(self.text_case);
        let gender = ctx.gender(self.variable.into());

        match value {
            Some(NumberOrPageVariableResult::Number(NumberVariableResult::Regular(
                MaybeTyped::Typed(num),
            ))) if num.will_transform() => {
                render_typed_num(num.as_ref(), self.form, gender, ctx);
            }

            Some(NumberOrPageVariableResult::Number(NumberVariableResult::Regular(
                MaybeTyped::Typed(num),
            ))) => write!(ctx, "{num}").unwrap(),

            Some(NumberOrPageVariableResult::Number(NumberVariableResult::Regular(
                MaybeTyped::String(s),
            ))) => ctx.push_str(&s),

            Some(NumberOrPageVariableResult::Number(
                NumberVariableResult::Transparent(n),
            )) => ctx.push_transparent(n),

            Some(NumberOrPageVariableResult::Page(MaybeTyped::Typed(p))) => {
                render_page_range(&p, ctx)
            }

            Some(NumberOrPageVariableResult::Page(MaybeTyped::String(s))) => {
                ctx.push_str(&s)
            }

            None => {}
        }

        ctx.pop_case(cidx);
        ctx.apply_suffix(&self.affixes, affix_loc, ambient);
        ctx.commit_elem(
            depth,
            self.display,
            Some(
                if self.variable
                    == NumberOrPageVariable::Number(NumberVariable::CitationNumber)
                {
                    ElemMeta::CitationNumber
                } else {
                    ElemMeta::Number
                },
            ),
        );
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        match ctx.instance.kind {
            Some(SpecialForm::VarOnly(Variable::Number(n)))
                if self.variable != NumberOrPageVariable::Number(n) =>
            {
                return false;
            }
            Some(SpecialForm::OnlyFirstDate | SpecialForm::OnlyYearSuffix) => {
                return matches!(
                    self.variable,
                    NumberOrPageVariable::Number(NumberVariable::Locator)
                );
            }
            Some(SpecialForm::VarOnly(_)) => return false,
            _ => {}
        }

        var == Variable::from(self.variable)
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        if self.will_render(ctx, self.variable.into()) {
            // If suppress_queried_variables is set to true, we need to perform a
            // silent lookup, otherwise we need to perform a regular lookup.
            let suppressing = ctx.writing.suppress_queried_variables;
            ctx.writing.stop_suppressing_queried_variables();
            let lookup_result = ctx.resolve_number_or_page_variable(self.variable);

            if suppressing {
                ctx.writing.start_suppressing_queried_variables();
            }

            (
                lookup_result.is_some(),
                UsageInfo {
                    has_vars: true,
                    has_non_empty_vars: lookup_result.is_some(),
                    ..Default::default()
                },
            )
        } else {
            (false, UsageInfo { has_vars: true, ..Default::default() })
        }
    }
}

fn render_typed_num<T: EntryLike>(
    num: &Numeric,
    form: NumberForm,
    gender: Option<GrammarGender>,
    ctx: &mut Context<T>,
) {
    let lookup = ctx.ordinal_lookup();
    num.with_form(&mut SuperscriptWriter(ctx), form, gender, &lookup)
        .unwrap();
}

/// A writer that renders Unicode superscript characters as superscript runs
/// with their baseline equivalents.
///
/// citeproc-js's HTML escaping maps characters like `ᵉ` to `<sup>e</sup>`, so
/// an ordinal suffix such as the French `ᵉ` becomes a superscript run. The
/// writer is used for ordinal terms; all other characters pass through
/// unchanged.
struct SuperscriptWriter<'a, 'b, T: EntryLike>(&'a mut Context<'b, T>);

impl<T: EntryLike> Write for SuperscriptWriter<'_, '_, T> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        push_with_superscripts(self.0, s);
        Ok(())
    }
}

/// Write `text`, rendering each Unicode superscript character as its own
/// superscript run with the lowered character. Characters without a
/// superscript equivalent pass through unchanged.
///
/// The mapping covers the characters used by CSL ordinal terms across the
/// bundled locales (`ª`, `º`, `ʳ`, `ᵉ`); citeproc-js applies the same
/// lowering to every superscript character in its output.
fn push_with_superscripts<T: EntryLike>(ctx: &mut Context<T>, text: &str) {
    let mut rest = text;
    while let Some((pos, c)) =
        rest.char_indices().find(|(_, c)| superscript_baseline(*c).is_some())
    {
        ctx.push_str(&rest[..pos]);
        let fmt = ctx.push_format(citationberg::Formatting {
            vertical_align: Some(citationberg::VerticalAlign::Sup),
            ..Default::default()
        });
        ctx.push_str(superscript_baseline(c).unwrap());
        ctx.pop_format(fmt);
        rest = &rest[pos + c.len_utf8()..];
    }

    ctx.push_str(rest);
}

/// The baseline equivalent of a Unicode superscript character used in CSL
/// ordinal terms.
fn superscript_baseline(c: char) -> Option<&'static str> {
    Some(match c {
        'ª' => "a",
        'º' => "o",
        'ʳ' => "r",
        'ᵉ' => "e",
        _ => return None,
    })
}

fn render_page_range<T: EntryLike>(range: &PageRanges, ctx: &mut Context<T>) {
    let format = ctx.style.csl.settings.page_range_format.unwrap_or_default();
    let delim = ctx
        .term(OtherTerm::PageRangeDelimiter.into(), TermForm::default(), false)
        .or(Some("–"));

    range
        .ranges
        .iter()
        .try_for_each(|r| match r {
            crate::PageRangesPart::Ampersand => ctx.write_str(" & "),
            crate::PageRangesPart::Comma => ctx.write_str(", "),
            crate::PageRangesPart::EscapedRange(start, end) => PageRangeFormat::Expanded
                .format(ctx, &start.to_string(), &end.to_string(), delim),
            crate::PageRangesPart::SinglePage(page) => ctx.write_str(&page.to_string()),
            crate::PageRangesPart::Range(start, end) => {
                format.format(ctx, &start.to_string(), &end.to_string(), delim)
            }
        })
        .unwrap();
}

fn label_pluralization(
    label: &citationberg::Label,
    variable: NumberVariableResult,
) -> bool {
    match label.label.plural {
        LabelPluralize::Always => true,
        LabelPluralize::Never => false,
        LabelPluralize::Contextual => match variable {
            NumberVariableResult::Regular(MaybeTyped::String(_)) => false,
            NumberVariableResult::Regular(MaybeTyped::Typed(n)) => {
                if let NumberOrPageVariable::Number(v) = label.variable {
                    n.is_plural(v.is_number_of_variable())
                } else {
                    panic!("Incompatible variable types")
                }
            }
            NumberVariableResult::Transparent(_) => false,
        },
    }
}

impl RenderCsl for citationberg::Label {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        if !self.will_have_info(ctx).0 {
            return;
        }

        match self.variable {
            NumberOrPageVariable::Number(n) => {
                let Some(variable) = ctx.resolve_number_variable(n) else {
                    return;
                };

                let depth = ctx.push_elem(citationberg::Formatting::default());
                let plural = label_pluralization(self, variable);

                let content = ctx
                    .term(Term::from(self.variable), self.label.form, plural)
                    .unwrap_or_default();

                render_label_with_var(&self.label, ctx, content);
                ctx.commit_elem(depth, None, Some(ElemMeta::Label));
            }
            NumberOrPageVariable::Page(pv) => {
                let Some(p) = ctx.resolve_page_variable(pv) else {
                    return;
                };

                let depth = ctx.push_elem(citationberg::Formatting::default());
                let plural = p.as_typed().is_some_and(|p| p.is_plural());

                let content =
                    ctx.term(Term::from(pv), self.label.form, plural).unwrap_or_default();

                render_label_with_var(&self.label, ctx, content);
                ctx.commit_elem(depth, None, Some(ElemMeta::Label));
            }
        }
    }

    fn will_render<T: EntryLike>(&self, _ctx: &mut Context<T>, _var: Variable) -> bool {
        false
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        match ctx.instance.kind {
            Some(SpecialForm::VarOnly(Variable::Number(n)))
                if self.variable != NumberOrPageVariable::Number(n) =>
            {
                return (false, UsageInfo::default());
            }
            Some(
                SpecialForm::VarOnly(_)
                | SpecialForm::OnlyFirstDate
                | SpecialForm::OnlyYearSuffix,
            ) if self.variable
                != NumberOrPageVariable::Number(NumberVariable::Locator) =>
            {
                return (true, UsageInfo::default());
            }
            _ => {}
        }

        // Never yield a label if the locator is set to custom.
        if self.variable == NumberOrPageVariable::Number(NumberVariable::Locator)
            && ctx
                .instance
                .cite_props
                .speculative
                .locator
                .as_ref()
                .is_some_and(|l| l.0 == Locator::Custom)
        {
            return (false, UsageInfo::default());
        }

        match self.variable {
            NumberOrPageVariable::Number(n) => {
                if let Some(num) = ctx.resolve_number_variable(n) {
                    let plural = label_pluralization(self, num);
                    (
                        ctx.term(Term::from(self.variable), self.label.form, plural)
                            .is_some(),
                        UsageInfo::default(),
                    )
                } else {
                    (false, UsageInfo::default())
                }
            }
            NumberOrPageVariable::Page(pv) => {
                if let Some(p) = ctx.resolve_page_variable(pv) {
                    let plural = p.as_typed().is_some_and(|p| p.is_plural());
                    (
                        ctx.term(Term::from(pv), self.label.form, plural).is_some(),
                        UsageInfo::default(),
                    )
                } else {
                    (false, UsageInfo::default())
                }
            }
        }
    }
}

fn render_label_with_var<T: EntryLike>(
    label: &citationberg::VariablelessLabel,
    ctx: &mut Context<T>,
    content: &str,
) {
    if content.is_empty() {
        return;
    }

    let ambient = *ctx.writing.formatting();
    let idx = ctx.push_format(label.formatting);

    let affixes = &label.affixes;
    let affix_loc = ctx.apply_prefix(affixes, ambient);

    ctx.may_strip_periods(label.strip_periods);
    let cidx = ctx.push_case(label.text_case);

    ctx.push_str(content);

    ctx.pop_case(cidx);
    ctx.stop_stripping_periods();
    ctx.apply_suffix(affixes, affix_loc, ambient);
    ctx.pop_format(idx);
}

impl RenderCsl for citationberg::Date {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        let Some(variable) = self.variable else { return };
        if !self.will_render(ctx, variable.into()) {
            return;
        }

        let Some(date) = ctx.resolve_date_variable(variable) else { return };

        if let Some(sorting) = ctx.instance.sorting {
            let year;
            let mut month = false;
            let mut day = false;

            if self.is_localized() {
                match self.parts {
                    Some(DateParts::Year) => year = true,
                    Some(DateParts::YearMonth) => {
                        year = true;
                        month = true;
                    }
                    Some(DateParts::YearMonthDay) | None => {
                        year = true;
                        month = true;
                        day = true;
                    }
                }
            } else if sorting == Sorting::Variable {
                // According to the CSL 1.0.2 spec (section "Sorting"):
                //
                // "Number variables rendered within the macro with cs:number
                // and date variables are treated the same as when they are
                // called via variable. The only exception is that the complete
                // date is returned if a date variable is called via the
                // variable attribute. In contrast, macros return only those
                // date-parts that would otherwise be rendered (...)."
                year = true;
                month = true;
                day = true;
            } else {
                year = self.date_part.iter().any(|i| i.name == DatePartName::Year);
                month = self.date_part.iter().any(|i| i.name == DatePartName::Month);
                day = self.date_part.iter().any(|i| i.name == DatePartName::Day);
            }

            if year {
                // Smart hack taken from citeproc: This prints negative (BC) dates as N(999,999,999 + y)
                // and positive (AD) dates as Py so they sort properly. (Use i32::MAX to avoid problems
                // with large dates.)
                let (prefix, yr) = if date.year < 0 {
                    ("N", i32::MAX + date.year)
                } else {
                    ("P", date.year)
                };
                write!(ctx, "{prefix}{yr:09}").unwrap();
                render_year_suffix_implicitly(ctx);
            }

            if month {
                write!(
                    ctx,
                    "{:02}",
                    date.month.map(|m| m as i32 + 1).unwrap_or_default()
                )
                .unwrap();
            }

            if day {
                write!(ctx, "{:02}", date.day.map(|d| d as i32 + 1).unwrap_or_default())
                    .unwrap();
            }

            return;
        }

        let base = if let Some(form) = self.form {
            // Localized date formats can fail to print anything at all,
            // especially if no locale is set.
            let Some(base) = ctx.localized_date(form) else { return };
            Some(base)
        } else {
            None
        };

        let first = ctx.is_first_date();
        let formatting = base
            .map(|b| self.formatting.apply(b.formatting))
            .unwrap_or(self.formatting);
        let ambient = *ctx.writing.formatting();
        let depth = ctx.push_elem(formatting);

        let affix_loc = ctx.apply_prefix(&self.affixes, ambient);

        let cidx = ctx.push_case(self.text_case.or(base.and_then(|b| b.text_case)));

        let parts = self.parts.or(base.and_then(|b| b.parts)).unwrap_or_default();

        // TODO: Date ranges
        let mut first_part = true;

        // Localized (base) delimiter takes precedence over the cs:date
        // element's delimiter attribute, which should be ignored if a locale's
        // date form is used, according to the CSL 1.0.2 spec (under "Style
        // Behavior"):
        //
        // "Delimiter
        //
        // The delimiter attribute, whose value delimits non-empty pieces of
        // output, may be set on cs:date (delimiting the date-parts; delimiter
        // is not allowed when cs:date calls a localized date format)"
        let chosen_delim = match base {
            Some(base) => base.delimiter.as_deref(),
            None => self.delimiter.as_deref(),
        };

        for part in &base.unwrap_or(self).date_part {
            match part.name {
                DatePartName::Month if !parts.has_month() && date.season.is_none() => {
                    continue;
                }
                DatePartName::Day if !parts.has_day() => continue,
                _ => {}
            }

            let over_ride = base
                .is_some()
                .then(|| self.date_part.iter().find(|p| p.name == part.name))
                .flatten();

            // Render the part in an isolated subtree so that the delimiter is
            // only printed when the part actually rendered something. A part
            // can be empty even after the checks above (e.g. a month without a
            // value), and pushing the delimiter unconditionally would leave a
            // trailing delimiter behind (`2021 ;14(2)`, F-114).
            let loc = ctx.push_elem(citationberg::Formatting::default());
            render_date_part(part, &date, ctx, over_ride, first);
            let delimiter = if first_part { None } else { chosen_delim };
            if ctx.commit_elem_with_delimiter(loc, delimiter) {
                first_part = false;
            }
        }

        ctx.pop_case(cidx);
        ctx.apply_suffix(&self.affixes, affix_loc, ambient);
        ctx.commit_elem(depth, self.display, Some(ElemMeta::Date));
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        match ctx.instance.kind {
            Some(SpecialForm::VarOnly(Variable::Date(d))) if self.variable != Some(d) => {
                return false;
            }
            Some(SpecialForm::OnlyFirstDate | SpecialForm::OnlyYearSuffix) => {
                return ctx.peek_is_first_date();
            }
            Some(SpecialForm::VarOnly(_)) => return false,
            _ => {}
        }

        Some(var) == self.variable.map(Variable::Date)
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        let suppressing = ctx.writing.suppress_queried_variables;
        ctx.writing.stop_suppressing_queried_variables();
        let Some(variable) = self.variable else {
            return (false, UsageInfo { has_vars: true, ..Default::default() });
        };

        if suppressing {
            ctx.writing.start_suppressing_queried_variables();
        }

        if !self.will_render(ctx, variable.into()) {
            (false, UsageInfo::default())
        } else {
            let base = self.form.and_then(|form| ctx.localized_date(form));
            let parts = self.parts.or(base.and_then(|b| b.parts)).unwrap_or_default();

            let has_non_empty_vars =
                ctx.resolve_date_variable(variable).is_some_and(|date| {
                    base.unwrap_or(self).date_part.iter().any(|part| match part.name {
                        DatePartName::Year => true,
                        DatePartName::Month => {
                            (parts.has_month() || date.season.is_some())
                                && (date.month.is_some() || date.season.is_some())
                        }
                        DatePartName::Day => parts.has_day() && date.day.is_some(),
                    })
                });
            (
                has_non_empty_vars,
                UsageInfo {
                    has_vars: true,
                    has_non_empty_vars,
                    ..Default::default()
                },
            )
        }
    }
}

fn render_date_part<T: EntryLike>(
    date_part: &citationberg::DatePart,
    date: &Date,
    ctx: &mut Context<T>,
    over_ride: Option<&citationberg::DatePart>,
    first: bool,
) {
    let Some(val) = (match date_part.name {
        DatePartName::Day => date.day.map(|i| i as i32 + 1),
        DatePartName::Month => {
            // Fallback for month is the season
            date.month
                .map(|i| i as i32 + 1)
                .or(date.season.map(|s| s.to_csl_number() as i32))
        }
        DatePartName::Year => Some(date.year),
    }) else {
        return;
    };

    let is_only_suffix = ctx.instance.kind == Some(SpecialForm::OnlyYearSuffix);
    let form = over_ride
        .map(citationberg::DatePart::form)
        .unwrap_or_else(|| date_part.form());

    let formatting = over_ride
        .map(|p| p.formatting.apply(date_part.formatting))
        .unwrap_or(date_part.formatting);

    let ambient = *ctx.writing.formatting();
    let idx = ctx.push_format(formatting);

    let affixes = &date_part.affixes;
    let affix_loc = (!is_only_suffix).then(|| ctx.apply_prefix(affixes, ambient));
    if date_part.name == DatePartName::Month {
        ctx.may_strip_periods(date_part.strip_periods);
    }

    let cidx = ctx.push_case(over_ride.and_then(|o| o.text_case).or(date_part.text_case));

    if !is_only_suffix {
        match form {
            DateStrongAnyForm::Month(_) if date.month.is_none() => {
                debug_assert!(date.season.is_some());
                let Some(season) = date.season else {
                    return;
                };
                let season_term = season.into();
                let Some(season) =
                    ctx.term(Term::Other(season_term), TermForm::Short, false)
                else {
                    return;
                };
                write!(ctx, "{season}").unwrap();
            }
            DateStrongAnyForm::Day(DateDayForm::NumericLeadingZeros)
            | DateStrongAnyForm::Month(DateMonthForm::NumericLeadingZeros) => {
                write!(ctx, "{val:02}").unwrap();
            }
            DateStrongAnyForm::Day(DateDayForm::Ordinal)
                if val == 1
                    || !ctx
                        .style
                        .lookup_locale(|l| l.style_options?.limit_day_ordinals_to_day_1)
                        .unwrap_or_default() =>
            {
                let gender = date
                    .month
                    .and_then(OtherTerm::month)
                    .and_then(|m| ctx.gender(m.into()));

                let suffix = ctx.ordinal_lookup().lookup(val, gender).unwrap_or_default();
                write!(ctx, "{val}").unwrap();
                push_with_superscripts(ctx, suffix);
            }
            DateStrongAnyForm::Day(DateDayForm::Numeric | DateDayForm::Ordinal)
            | DateStrongAnyForm::Month(DateMonthForm::Numeric) => {
                write!(ctx, "{val}").unwrap();
            }
            DateStrongAnyForm::Month(DateMonthForm::Long) => {
                if let Some(month) = OtherTerm::month((val - 1) as u8)
                    .and_then(|m| ctx.term(m.into(), TermForm::Long, false))
                {
                    ctx.push_str(month);
                } else {
                    write!(ctx, "{val}").unwrap();
                }
            }
            DateStrongAnyForm::Month(DateMonthForm::Short) => {
                if let Some(month) = OtherTerm::month((val - 1) as u8)
                    .and_then(|m| ctx.term(m.into(), TermForm::Short, false))
                {
                    ctx.push_str(month);
                } else {
                    write!(ctx, "{val}").unwrap();
                }
            }
            DateStrongAnyForm::Year(brevity) => {
                let ad = ctx
                    .term(Term::Other(OtherTerm::Ad), TermForm::default(), false)
                    .unwrap_or(" AD");
                let bc = ctx
                    .term(Term::Other(OtherTerm::Bc), TermForm::default(), false)
                    .unwrap_or(" BC");
                write_year(val, brevity == LongShortForm::Short, ctx, ad, bc).unwrap();
            }
        }
    }

    if let DateStrongAnyForm::Year(_) = form
        && first
    {
        render_year_suffix_implicitly(ctx);
    }

    if let Some(affix_loc) = affix_loc {
        ctx.apply_suffix(affixes, affix_loc, ambient);
    }
    ctx.stop_stripping_periods();
    ctx.pop_case(cidx);
    ctx.pop_format(idx);
}

/// Render the year suffix if it is set and the style will not render it
/// explicitly.
fn render_year_suffix_implicitly<T: EntryLike>(ctx: &mut Context<T>) {
    if ctx.renders_year_suffix_implicitly()
        && let Some(year_suffix) = ctx.resolve_standard_variable(
            LongShortForm::default(),
            StandardVariable::YearSuffix,
        )
    {
        ctx.push_chunked(year_suffix.as_ref());
    }
}

fn choose_children<F, R, T: EntryLike>(
    choose: &citationberg::Choose,
    ctx: &mut Context<T>,
    mut f: F,
) -> Option<R>
where
    F: FnMut(&[LayoutRenderingElement], &mut Context<T>) -> R,
{
    let suppressed = ctx.writing.suppress_queried_variables;
    ctx.writing.stop_suppressing_queried_variables();
    let branch = choose
        .branches()
        .find(|branch| branch.match_.test(BranchConditionIter::from_branch(branch, ctx)));
    ctx.writing.suppress_queried_variables = suppressed;

    branch
        .map(|b| b.children.as_slice())
        .or_else(|| choose.otherwise.as_ref().map(|f| f.children.as_slice()))
        .map(|children| f(children, ctx))
}

impl RenderCsl for citationberg::Choose {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        choose_children(self, ctx, |children, ctx| {
            // Propagate parent group's delimiter to 'choose' output, as
            // required by CSL, by not pushing a delimiter to the stack.
            render_with_delimiter(children, ctx);
        });
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        choose_children(self, ctx, |children, ctx| {
            children.iter().any(|c| c.will_render(ctx, var))
        })
        .unwrap_or_default()
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        choose_children(self, ctx, |children, ctx| {
            let mut info = UsageInfo::default();
            let mut will_print = false;

            for child in children {
                let (print, child_info) = child.will_have_info(ctx);
                will_print |= print;
                info = info.merge_child(child_info);
            }

            (will_print, info)
        })
        .unwrap_or_else(|| (false, UsageInfo::default()))
    }
}

/// Render `children` with the delimiter in `ctx` between them.
///
/// The delimiter can be updated by [`ctx.writing.push_delimiter`][super::WritingContext::push_delimiter]
/// and [`ctx.writing.pop_delimiter`][super::WritingContext::pop_delimiter].
fn render_with_delimiter<T: EntryLike>(
    children: &[LayoutRenderingElement],
    ctx: &mut Context<T>,
) {
    let delimiter = ctx.writing.delimiters.last().clone();

    let mut first = true;
    let mut loc = None;

    for child in children {
        // Do not render the child if it will not print anything.
        if !child.will_have_info(ctx).0 {
            continue;
        }

        if !first && let Some(delim) = &delimiter {
            let prev_loc = std::mem::take(&mut loc);

            if let Some(prev_loc) = prev_loc {
                ctx.commit_elem(prev_loc, None, None);
            }

            loc = Some(ctx.push_elem(citationberg::Formatting::default()));
            ctx.push_str(delim);
        }
        first = false;

        let pos = ctx.push_elem(citationberg::Formatting::default());
        child.render(ctx);
        ctx.commit_elem(pos, None, None);
    }

    if let Some(loc) = loc {
        ctx.commit_elem(loc, None, None);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BranchConditionPos {
    Disambiguate,
    IsNumeric,
    IsUncertainDate,
    Locator,
    Position,
    Type,
    Variable,
}

impl Iterator for BranchConditionPos {
    type Item = Self;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Disambiguate => {
                *self = Self::IsNumeric;
                Some(Self::Disambiguate)
            }
            Self::IsNumeric => {
                *self = Self::IsUncertainDate;
                Some(Self::IsNumeric)
            }
            Self::IsUncertainDate => {
                *self = Self::Locator;
                Some(Self::IsUncertainDate)
            }
            Self::Locator => {
                *self = Self::Position;
                Some(Self::Locator)
            }
            Self::Position => {
                *self = Self::Type;
                Some(Self::Position)
            }
            Self::Type => {
                *self = Self::Variable;
                Some(Self::Type)
            }
            Self::Variable => None,
        }
    }
}

struct BranchConditionIter<'a, 'b, T: EntryLike> {
    cond: &'a ChooseBranch,
    ctx: &'a mut Context<'b, T>,
    pos: BranchConditionPos,
    idx: usize,
}

impl<'a, 'b, T: EntryLike> BranchConditionIter<'a, 'b, T> {
    fn from_branch(cond: &'a ChooseBranch, ctx: &'a mut Context<'b, T>) -> Self {
        Self {
            cond,
            ctx,
            pos: BranchConditionPos::Disambiguate,
            idx: 0,
        }
    }

    fn next_case(&mut self) {
        self.pos.next();
        self.idx = 0;
    }
}

impl<T: EntryLike> Iterator for BranchConditionIter<'_, '_, T> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pos {
            BranchConditionPos::Disambiguate => {
                self.pos.next();
                if let Some(d) = self.cond.disambiguate {
                    Some(d == self.ctx.should_disambiguate())
                } else {
                    self.next()
                }
            }
            BranchConditionPos::IsNumeric => {
                if let Some(vars) = &self.cond.is_numeric {
                    if self.idx >= vars.len() {
                        self.next_case();
                        return self.next();
                    }

                    let var = vars[self.idx];
                    self.idx += 1;

                    Some(match var {
                        Variable::Standard(var) => self
                            .ctx
                            .resolve_standard_variable(LongShortForm::default(), var)
                            .map(|v| Numeric::from_str(&v.to_string()).is_ok())
                            .unwrap_or_default(),
                        Variable::Number(var) => matches!(
                            self.ctx.resolve_number_variable(var),
                            Some(NumberVariableResult::Regular(MaybeTyped::Typed(_)))
                        ),
                        Variable::Page(var) => matches!(
                            self.ctx.resolve_page_variable(var),
                            Some(MaybeTyped::Typed(_))
                        ),
                        _ => false,
                    })
                } else {
                    self.next_case();
                    self.next()
                }
            }
            BranchConditionPos::IsUncertainDate => {
                if let Some(vars) = &self.cond.is_uncertain_date {
                    if self.idx >= vars.len() {
                        self.next_case();
                        return self.next();
                    }

                    let var = vars[self.idx];
                    self.idx += 1;

                    Some(
                        self.ctx
                            .resolve_date_variable(var)
                            .is_some_and(|d| d.approximate),
                    )
                } else {
                    self.next_case();
                    self.next()
                }
            }
            BranchConditionPos::Locator => {
                if let Some(locs) = &self.cond.locator {
                    if self.idx >= locs.len() {
                        self.next_case();
                        return self.next();
                    }

                    let loc = locs[self.idx];
                    self.idx += 1;

                    Some(
                        self.ctx
                            .instance
                            .cite_props
                            .speculative
                            .locator
                            .as_ref()
                            .is_some_and(|l| l.0 == loc),
                    )
                } else {
                    self.next_case();
                    self.next()
                }
            }
            BranchConditionPos::Position => {
                if let Some(pos) = &self.cond.position {
                    // CSL 1.0.2 spec ("Choose" > "position"): "When called
                    // within the scope of cs:bibliography, position tests
                    // 'false'."
                    if self.ctx.bibliography || self.idx >= pos.len() {
                        self.next_case();
                        return self.next();
                    }

                    let spec_pos = pos[self.idx];
                    self.idx += 1;

                    let props = &self.ctx.instance.cite_props;

                    Some(match spec_pos {
                        TestPosition::First => props.certain.is_first,
                        TestPosition::Subsequent => !props.certain.is_first,
                        TestPosition::Ibid => {
                            matches!(
                                props.speculative.ibid,
                                IbidState::Ibid | IbidState::IbidWithLocator
                            )
                        }
                        TestPosition::IbidWithLocator => {
                            matches!(props.speculative.ibid, IbidState::IbidWithLocator)
                        }
                        TestPosition::NearNote => props.certain.is_near_note,
                    })
                } else {
                    self.next_case();
                    self.next()
                }
            }
            BranchConditionPos::Type => {
                if let Some(kinds) = &self.cond.type_ {
                    if self.idx >= kinds.len() {
                        self.next_case();
                        return self.next();
                    }

                    // citeproc-js always combines the values of a `type`
                    // attribute with "any" semantics, regardless of the
                    // branch's `match` policy (`type="book report"` is true
                    // for books even under the default `match="all"`).
                    let mut matched = false;
                    while self.idx < kinds.len() {
                        let kind = kinds[self.idx];
                        self.idx += 1;
                        matched |= self.ctx.instance.entry.matches_entry_type(kind);
                    }

                    Some(matched)
                } else {
                    self.next_case();
                    self.next()
                }
            }
            BranchConditionPos::Variable => {
                if let Some(vars) = &self.cond.variable {
                    if self.idx >= vars.len() {
                        return None;
                    }

                    let var = vars[self.idx];
                    self.idx += 1;

                    Some(match var {
                        Variable::Standard(s) => {
                            let val = self
                                .ctx
                                .resolve_standard_variable(LongShortForm::default(), s);
                            val.is_some_and(|s| {
                                !s.to_string().chars().all(char::is_whitespace)
                            })
                        }
                        Variable::Number(n) => {
                            let val = self.ctx.resolve_number_variable(n);
                            val.is_some()
                        }
                        Variable::Date(d) => self.ctx.resolve_date_variable(d).is_some(),
                        Variable::Name(n) => {
                            !self.ctx.resolve_name_variable(n).is_empty()
                        }
                        Variable::Page(pv) => {
                            self.ctx.resolve_page_variable(pv).is_some()
                        }
                    })
                } else {
                    None
                }
            }
        }
    }
}

impl RenderCsl for citationberg::Group {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        let ambient = *ctx.writing.formatting();
        // The outer element holds the affixes; citeproc-js writes them outside
        // the group's formatting tags (F-116).
        let idx = ctx.push_elem(citationberg::Formatting::default());
        let affixes = self.to_affixes();

        let affix_loc = ctx.apply_prefix(&affixes, ambient);

        let info = self.will_have_info(ctx).1;

        // citeproc-js opens one formatting tag pair per declaration and keeps
        // it open for everything that inherits it. In bibliography entries the
        // declaration is recorded as a scope on the element so that adjacent
        // leaves inside it render as one run (`<i>2nd Edition</i>` instead of
        // `<i>2nd </i><i>Edition</i>`, F-122), and so that a child which
        // re-declares formatting gets its own nested pair, as citeproc-js
        // does. Citation trees keep their leaves fully formatted and record
        // no scopes, as before.
        let scope = ctx.push_scoped_elem(self.to_formatting());

        let delim_idx = ctx.writing.push_delimiter(self.delimiter.clone());
        render_with_delimiter(&self.children, ctx);
        ctx.writing.pop_delimiter(delim_idx);

        // Close the formatting scope before writing the suffix so that the
        // affixes stay outside of it.
        ctx.commit_elem(scope, None, None);

        ctx.apply_suffix(&affixes, affix_loc, ambient);

        if info.should_render_group() {
            ctx.commit_elem(idx, self.display, None);
        } else {
            ctx.discard_elem(idx);
        }
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        self.children.iter().any(|e| e.will_render(ctx, var))
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        let mut info = UsageInfo::default();
        let mut will_print = false;

        for child in &self.children {
            let (print, child_info) = child.will_have_info(ctx);
            will_print |= print;
            info = info.merge_child(child_info);

            match child {
                citationberg::LayoutRenderingElement::Group(_) if print => {
                    info.has_non_empty_group = true;
                }
                _ => {}
            }
        }

        will_print &= info.should_render_group();

        (will_print, info)
    }
}

impl RenderCsl for citationberg::LayoutRenderingElement {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        match self {
            citationberg::LayoutRenderingElement::Text(text) => text.render(ctx),
            citationberg::LayoutRenderingElement::Number(num) => num.render(ctx),
            citationberg::LayoutRenderingElement::Label(label) => label.render(ctx),
            citationberg::LayoutRenderingElement::Date(date) => date.render(ctx),
            citationberg::LayoutRenderingElement::Names(names) => names.render(ctx),
            citationberg::LayoutRenderingElement::Choose(choose) => choose.render(ctx),
            citationberg::LayoutRenderingElement::Group(group) => group.render(ctx),
        }
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        match self {
            citationberg::LayoutRenderingElement::Text(text) => {
                text.will_render(ctx, var)
            }
            citationberg::LayoutRenderingElement::Number(num) => {
                num.will_render(ctx, var)
            }
            citationberg::LayoutRenderingElement::Label(label) => {
                label.will_render(ctx, var)
            }
            citationberg::LayoutRenderingElement::Date(date) => {
                date.will_render(ctx, var)
            }
            citationberg::LayoutRenderingElement::Names(names) => {
                names.will_render(ctx, var)
            }
            citationberg::LayoutRenderingElement::Choose(choose) => {
                choose.will_render(ctx, var)
            }
            citationberg::LayoutRenderingElement::Group(group) => {
                group.will_render(ctx, var)
            }
        }
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        match self {
            citationberg::LayoutRenderingElement::Text(text) => text.will_have_info(ctx),
            citationberg::LayoutRenderingElement::Number(num) => num.will_have_info(ctx),
            citationberg::LayoutRenderingElement::Label(label) => {
                label.will_have_info(ctx)
            }
            citationberg::LayoutRenderingElement::Date(date) => date.will_have_info(ctx),
            citationberg::LayoutRenderingElement::Names(names) => {
                names.will_have_info(ctx)
            }
            citationberg::LayoutRenderingElement::Choose(choose) => {
                choose.will_have_info(ctx)
            }
            citationberg::LayoutRenderingElement::Group(group) => {
                group.will_have_info(ctx)
            }
        }
    }
}

impl RenderCsl for citationberg::Layout {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        let format_idx = ctx.push_format(self.to_formatting());
        // The layout delimiter joins the cites of one citation (handled by the
        // driver). citeproc-js does not delimit the layout's own children or
        // the branches of a top-level `cs:choose` with it (F-123), so it must
        // not be visible to them: only `cs:group` exposes a delimiter.
        let delim_idx = ctx.writing.push_delimiter(None);
        for e in &self.elements {
            e.render(ctx);
        }
        ctx.writing.pop_delimiter(delim_idx);
        ctx.pop_format(format_idx);
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        self.elements.iter().any(|e| e.will_render(ctx, var))
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        let mut info = UsageInfo::default();
        let mut will_print = false;

        for child in &self.elements {
            let (print, child_info) = child.will_have_info(ctx);
            will_print |= print;
            info = info.merge_child(child_info);
        }

        (will_print, info)
    }
}

impl RenderCsl for citationberg::RenderingElement {
    fn render<T: EntryLike>(&self, ctx: &mut Context<T>) {
        match self {
            citationberg::RenderingElement::Layout(l) => l.render(ctx),
            citationberg::RenderingElement::Other(o) => o.render(ctx),
        }
    }

    fn will_render<T: EntryLike>(&self, ctx: &mut Context<T>, var: Variable) -> bool {
        match self {
            citationberg::RenderingElement::Layout(l) => l.will_render(ctx, var),
            citationberg::RenderingElement::Other(o) => o.will_render(ctx, var),
        }
    }

    fn will_have_info<T: EntryLike>(&self, ctx: &mut Context<T>) -> (bool, UsageInfo) {
        match self {
            citationberg::RenderingElement::Layout(l) => l.will_have_info(ctx),
            citationberg::RenderingElement::Other(o) => o.will_have_info(ctx),
        }
    }
}

impl From<TextCase> for Case {
    fn from(case: TextCase) -> Self {
        match case {
            TextCase::Uppercase => Case::Uppercase,
            TextCase::Lowercase => Case::Lowercase,
            TextCase::TitleCase => Case::Title(TitleCase::default()),
            TextCase::SentenceCase => Case::Sentence(SentenceCase::default()),
            TextCase::CapitalizeFirst => Case::FirstUpper,
            TextCase::CapitalizeAll => Case::AllUpper,
        }
    }
}
