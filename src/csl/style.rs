//! A documented local fallback for the citeproc-js `date-parts="month-day"`
//! form.
//!
//! CSL 1.0.2 and `citationberg` 0.7 model only `year-month-day`,
//! `year-month` and `year` ([`citationberg::DateParts`]); they cannot parse
//! `date-parts="month-day"`, which citeproc-js accepts on a localized
//! `<date form="…">`. This module keeps `citationberg` unchanged and expands
//! the missing form instead:
//!
//! [`independent_style_with_month_day`] parses a style with the attribute
//! rewritten to a form `citationberg` accepts, then rebuilds each marked date
//! node from the locale's localized date template with the year removed,
//! mirroring citeproc-js's `CSL.Util.fixDateNode`:
//!
//! * the template's `month` and `day` parts are copied (their locale forms
//!   and delimiters survive),
//! * the year part is removed,
//! * the suffix of the part before the year is cleared, so a text date renders
//!   `January 15` rather than `January 15, `,
//! * the style's own `<date-part>` overrides are applied on top.
//!
//! # Limitations
//!
//! The expanded node is a standalone (non-localized) date, because
//! `citationberg`'s localized date path has no way to exclude the year. As a
//! consequence a `<date-part>` override contributes its *effective* form
//! (`citationberg` keeps the declared form private), and a locale date
//! template's own formatting/text case is merged into the style date instead
//! of being layered at render time. Both are equivalent for the forms the
//! audit needs; unsupported styles keep parsing through
//! [`citationberg::IndependentStyle::from_xml`] unchanged.

use citationberg::{
    Affixes, Date, DatePart, DatePartName, IndependentStyle, Locale, XmlDeError,
};

/// A private-use marker written into the `delimiter` attribute while parsing.
///
/// `citationberg` ignores unknown attributes, but it preserves the
/// `delimiter` string, so the marker survives parsing and identifies the date
/// nodes that carried `date-parts="month-day"`. It is stripped again by
/// [`expand_dates`] before the style is returned.
const MARKER: &str = "\u{e000}hayagriva-month-day";

/// Parse an independent style, expanding citeproc-js's
/// `date-parts="month-day"` form with the date template of `locale`.
///
/// Styles without the form are parsed exactly like
/// [`citationberg::IndependentStyle::from_xml`]. See the module documentation
/// for the expansion and its limitations.
pub fn independent_style_with_month_day(
    xml: &str,
    locale: &Locale,
) -> Result<IndependentStyle, XmlDeError> {
    let (xml, marked) = mark_month_day_dates(xml);
    let mut style = IndependentStyle::from_xml(&xml)?;
    if marked {
        expand_dates(&mut style, locale);
    }
    Ok(style)
}

/// Rewrite every `date-parts="month-day"` to a parseable value and mark its
/// `<date>` element through a sentinel `delimiter` attribute.
///
/// Returns the rewritten XML and whether any occurrence was found.
fn mark_month_day_dates(xml: &str) -> (String, bool) {
    const ATTR: &str = r#"date-parts="month-day""#;
    if !xml.contains(ATTR) {
        return (xml.to_owned(), false);
    }

    let mut out = String::with_capacity(xml.len() + 32);
    let mut rest = xml;
    while let Some(pos) = rest.find(ATTR) {
        // The occurrence is inside a tag; the nearest `<` starts it.
        let tag_start = rest[..pos].rfind('<').unwrap_or(0);
        let Some(tag_len) = tag_len(&rest[tag_start..]) else {
            break;
        };
        let tag_end = tag_start + tag_len;
        let tag =
            rest[tag_start..tag_end].replace(ATTR, r#"date-parts="year-month-day""#);
        out.push_str(&rest[..tag_start]);
        out.push_str(&mark_delimiter(&tag));
        rest = &rest[tag_end..];
    }
    out.push_str(rest);
    (out, true)
}

/// Length in bytes of the tag starting at `s[0] == '<'`, including `>`.
fn tag_len(s: &str) -> Option<usize> {
    let mut quote = None;
    for (idx, character) in s.char_indices().skip(1) {
        match character {
            '"' | '\'' if quote == Some(character) => quote = None,
            '"' | '\'' if quote.is_none() => quote = Some(character),
            '>' if quote.is_none() => return Some(idx + 1),
            _ => {}
        }
    }
    None
}

/// Insert the [`MARKER`] into the tag's `delimiter` attribute (prepended, so
/// an existing delimiter is preserved after the marker).
fn mark_delimiter(tag: &str) -> String {
    if let Some(quote) = delimiter_quote(tag) {
        let at = quote + 1;
        let mut marked = String::with_capacity(tag.len() + MARKER.len());
        marked.push_str(&tag[..at]);
        marked.push_str(MARKER);
        marked.push_str(&tag[at..]);
        return marked;
    }

    // No delimiter: add one before the closing `>`/`/>`.
    let close = tag.rfind('>').unwrap_or(tag.len());
    let insert = if tag[..close].ends_with('/') { close - 1 } else { close };
    let mut marked = String::with_capacity(tag.len() + MARKER.len() + 16);
    marked.push_str(&tag[..insert]);
    marked.push_str(" delimiter=\"");
    marked.push_str(MARKER);
    marked.push_str("\"");
    marked.push_str(&tag[insert..]);
    marked
}

/// Byte index of the opening quote of the tag's `delimiter` attribute value.
fn delimiter_quote(tag: &str) -> Option<usize> {
    let mut rest = tag;
    let mut offset = 0;
    while let Some(pos) = rest.find("delimiter") {
        let abs = offset + pos;
        let before_ok = abs == 0
            || tag[..abs]
                .chars()
                .next_back()
                .is_some_and(|c| c.is_whitespace() || c == '<');
        let after = &tag[abs + "delimiter".len()..];
        let after_trimmed = after.trim_start();
        if before_ok && after_trimmed.starts_with('=') {
            let value = after_trimmed[1..].trim_start();
            let quote_at = tag.len() - value.len();
            return value.starts_with('"').then_some(quote_at);
        }
        offset = abs + "delimiter".len();
        rest = &tag[offset..];
    }
    None
}

/// Expand every marked date node in the style with `locale`'s date template.
fn expand_dates(style: &mut IndependentStyle, locale: &Locale) {
    for mac in &mut style.macros {
        expand_elements(&mut mac.children, locale);
    }
    expand_elements(&mut style.citation.layout.elements, locale);
    if let Some(bibliography) = &mut style.bibliography {
        expand_elements(&mut bibliography.layout.elements, locale);
    }
}

/// Walk a rendering-element list, expanding marked dates (and their
/// containers: groups, choose branches and name substitutes).
fn expand_elements(
    elements: &mut [citationberg::LayoutRenderingElement],
    locale: &Locale,
) {
    use citationberg::LayoutRenderingElement as El;

    for element in elements {
        match element {
            El::Date(date) => expand_date(date, locale),
            El::Group(group) => expand_elements(&mut group.children, locale),
            El::Choose(choose) => {
                expand_elements(&mut choose.if_.children, locale);
                for branch in &mut choose.else_if {
                    expand_elements(&mut branch.children, locale);
                }
                if let Some(otherwise) = &mut choose.otherwise {
                    expand_elements(&mut otherwise.children, locale);
                }
            }
            El::Names(names) => {
                for child in &mut names.children {
                    if let citationberg::NamesChild::Substitute(substitute) = child {
                        expand_elements(&mut substitute.children, locale);
                    }
                }
            }
            El::Text(_) | El::Number(_) | El::Label(_) => {}
        }
    }
}

/// Expand one marked `date-parts="month-day"` date node.
fn expand_date(date: &mut Date, locale: &Locale) {
    let Some(delimiter) = date.delimiter.take() else {
        return;
    };
    let Some(original) = delimiter.strip_prefix(MARKER) else {
        date.delimiter = Some(delimiter);
        return;
    };
    date.delimiter = (!original.is_empty()).then(|| original.to_owned());

    // Without `form` the date is standalone and citeproc-js ignores
    // `date-parts`; the rewritten `year-month-day` value is already the right
    // parse for that shape.
    let Some(form) = date.form else {
        return;
    };
    let Some(template) = locale
        .date
        .iter()
        .find(|template| template.form == Some(form))
        .cloned()
    else {
        return;
    };

    let mut parts: Vec<DatePart> = Vec::with_capacity(template.date_part.len());
    for part in &template.date_part {
        if part.name == DatePartName::Year {
            // citeproc-js clears the suffix of the part in front of the year
            // before deleting it (`January 15`, not `January 15, `).
            if let Some(previous) = parts.last_mut() {
                previous.affixes.suffix = None;
            }
            continue;
        }
        let over_ride = date.date_part.iter().find(|o| o.name == part.name);
        parts.push(merge_part(part, over_ride));
    }

    // Merge the locale date template's own declarations the way the localized
    // renderer layers them: the style's declared values win.
    date.formatting = date.formatting.apply(template.formatting);
    if date.text_case.is_none() {
        date.text_case = template.text_case;
    }
    if date.delimiter.is_none() {
        date.delimiter = template.delimiter;
    }
    date.date_part = parts;
    date.form = None;
    date.parts = None;
}

/// Merge a style `<date-part>` override onto the locale template part.
///
/// The override supplies its form (which `citationberg` keeps private) and any
/// declared formatting/affixes; the locale part supplies everything the style
/// did not redeclare, notably the delimiters that make a localized date read
/// correctly.
fn merge_part(locale: &DatePart, over_ride: Option<&DatePart>) -> DatePart {
    let Some(over_ride) = over_ride else {
        return locale.clone();
    };

    let mut part = over_ride.clone();
    part.affixes = Affixes {
        prefix: over_ride
            .affixes
            .prefix
            .clone()
            .or_else(|| locale.affixes.prefix.clone()),
        suffix: over_ride
            .affixes
            .suffix
            .clone()
            .or_else(|| locale.affixes.suffix.clone()),
    };
    part.formatting = over_ride.formatting.apply(locale.formatting);
    part.range_delimiter = over_ride
        .range_delimiter
        .clone()
        .or_else(|| locale.range_delimiter.clone());
    part.strip_periods |= locale.strip_periods;
    part.text_case = over_ride.text_case.or(locale.text_case);
    part
}

#[cfg(test)]
mod tests {
    use super::*;
    use citationberg::LocaleFile;

    fn en_us() -> Locale {
        let xml = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/data/locales-en-US.xml"),
        )
        .unwrap();
        Locale::from(LocaleFile::from_xml(&xml).unwrap())
    }

    fn style_xml(date_parts: &str) -> String {
        format!(
            r#"<style xmlns="http://purl.org/net/xbiblio/csl" class="in-text" version="1.0">
                 <info><id/><title/><updated>2009-08-10T04:49:00+09:00</updated></info>
                 <citation><layout><text value="X"/></layout></citation>
                 <bibliography>
                   <layout>
                     <date variable="issued" form="text" date-parts="{date_parts}"/>
                   </layout>
                 </bibliography>
               </style>"#
        )
    }

    fn render_month_day(xml: &str, locale: &Locale, issued: &str) -> String {
        use crate::{
            BibliographyDriver, BibliographyRequest, CitationItem, CitationRequest,
        };

        let style = independent_style_with_month_day(xml, locale).unwrap();
        let library = crate::io::from_yaml_str(&format!(
            r#"a:
                 type: Book
                 title: Example
                 date: {issued}
            "#
        ))
        .unwrap();
        let entry = library.get("a").unwrap();

        let mut driver = BibliographyDriver::new();
        driver.citation(CitationRequest::new(
            vec![CitationItem::with_entry(entry)],
            &style,
            Some(citationberg::LocaleCode::en_us()),
            std::slice::from_ref(locale),
            None,
        ));
        let rendered = driver.finish(BibliographyRequest::new(
            &style,
            Some(citationberg::LocaleCode::en_us()),
            std::slice::from_ref(locale),
        ));
        let mut output = String::new();
        rendered.bibliography.as_ref().unwrap().items[0]
            .content
            .write_buf(&mut output, crate::BufWriteFormat::Plain)
            .unwrap();
        output
    }

    #[test]
    fn month_day_text_date_omits_the_year_and_trailing_separator() {
        let locale = en_us();
        let output = render_month_day(&style_xml("month-day"), &locale, "2020-01-15");
        assert_eq!(output, "January 15");
    }

    #[test]
    fn month_day_date_keeps_its_own_date_part_override() {
        // A style month-form override applies to the expanded month part.
        let xml = style_xml("month-day").replace(
            r#"date variable="issued" form="text" date-parts="month-day"/>"#,
            r#"date variable="issued" form="text" date-parts="month-day">
                     <date-part name="month" form="short"/>
                   </date>"#,
        );
        let locale = en_us();
        let output = render_month_day(&xml, &locale, "2020-01-15");
        assert_eq!(output, "Jan. 15");
    }

    #[test]
    fn month_day_does_not_change_other_date_forms() {
        let locale = en_us();
        let output =
            render_month_day(&style_xml("year-month-day"), &locale, "2020-01-15");
        assert_eq!(output, "January 15, 2020");
    }
}
