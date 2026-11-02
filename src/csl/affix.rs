//! Rich-text citation-item affixes.
//!
//! citeproc-js parses a small HTML subset in per-item `prefix`/`suffix`
//! values (`<i>`, `<b>`, `<sc>`, `<sup>`, `<sub>`, and the `span` forms
//! citeproc-js recognizes) and splices the resulting formatted runs into the
//! citation. [`Affix`] carries those runs; a plain string remains a single
//! unformatted run so existing callers keep working.

use std::fmt::{self, Display};

use citationberg::{
    FontStyle, FontVariant, FontWeight, Formatting, TextDecoration, VerticalAlign,
};

use super::attribute_value;

/// One formatted run of a rich-text affix.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AffixRun {
    /// The literal text of the run.
    pub text: String,
    /// The formatting parsed from citeproc-js rich-text markup.
    ///
    /// Uses `citationberg`'s partial formatting so unset fields inherit the
    /// surrounding citation formatting.
    pub formatting: Formatting,
}

/// A citation-item affix that may carry citeproc-js rich-text markup.
///
/// [`Affix::parse`] turns `<i>`, `<b>`, `<sc>`, `<sup>` and `<sub>` tags into
/// formatted runs; any other markup is kept as literal text.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Affix {
    runs: Vec<AffixRun>,
}

impl Affix {
    /// Create an affix from a plain string (no markup is interpreted).
    pub fn plain(text: impl Into<String>) -> Self {
        let text = text.into();
        if text.is_empty() {
            Self::default()
        } else {
            Self {
                runs: vec![AffixRun { text, formatting: Formatting::default() }],
            }
        }
    }

    /// Parse citeproc-js rich-text markup into formatted runs.
    ///
    /// Supported tags are `<i>` (italic), `<b>` (bold), `<sc>` (small caps),
    /// `<sup>` (superscript), `<sub>` (subscript), `<span class="nocase">`
    /// (text case only), `<span class="nodecor">` (reset all decorations) and
    /// `<span style="…">` with the CSS properties citeproc-js understands.
    /// Tags nest, and `</span>` closes the innermost span scope whatever it
    /// declared. Unrecognized tags stay in the text verbatim.
    pub fn parse(text: impl AsRef<str>) -> Self {
        let text = text.as_ref();
        let mut runs: Vec<AffixRun> = Vec::new();
        let mut buf = String::new();
        let mut formatting = Formatting::default();
        let mut stack: Vec<(MarkupTag, Formatting)> = Vec::new();

        let flush =
            |runs: &mut Vec<AffixRun>, buf: &mut String, formatting: Formatting| {
                if !buf.is_empty() {
                    runs.push(AffixRun { text: std::mem::take(buf), formatting });
                }
            };

        let mut rest = text;
        while let Some(start) = rest.find('<') {
            let Some(end) = rest[start..].find('>') else { break };
            let tag = &rest[start + 1..start + end];
            let Some((tag, closing)) = MarkupTag::parse(tag) else {
                // Not a supported tag: keep the `<` as literal text and
                // continue scanning after it.
                buf.push_str(&rest[..start + 1]);
                rest = &rest[start + 1..];
                continue;
            };

            buf.push_str(&rest[..start]);
            flush(&mut runs, &mut buf, formatting);
            if closing {
                if let Some(pos) =
                    stack.iter().rposition(|(open, _)| open.matches_close(tag))
                {
                    formatting = stack[pos].1;
                    stack.truncate(pos);
                } else {
                    // A closing tag without a matching scope stays literal,
                    // like an unrecognized tag (`<span>` without a recognized
                    // class/style is not a scope, so its `</span>` must not
                    // vanish).
                    buf.push_str(&rest[start..start + end + 1]);
                }
            } else {
                stack.push((tag, formatting));
                formatting = overlay(formatting, tag.formatting());
            }
            rest = &rest[start + end + 1..];
        }
        buf.push_str(rest);
        flush(&mut runs, &mut buf, formatting);

        Self { runs }
    }

    /// The formatted runs of this affix.
    pub fn runs(&self) -> &[AffixRun] {
        &self.runs
    }

    /// Whether the affix carries no text.
    pub fn is_empty(&self) -> bool {
        self.runs.iter().all(|run| run.text.is_empty())
    }

    /// The affix as unformatted text.
    pub fn as_plain(&self) -> String {
        let mut text = String::new();
        for run in &self.runs {
            text.push_str(&run.text);
        }
        text
    }

    /// The first character of the affix's text.
    pub fn first_char(&self) -> Option<char> {
        self.runs.iter().find_map(|run| run.text.chars().next())
    }

    /// The last character of the affix's text.
    pub fn last_char(&self) -> Option<char> {
        self.runs.iter().rev().find_map(|run| run.text.chars().next_back())
    }
}

impl From<&str> for Affix {
    fn from(text: &str) -> Self {
        Self::parse(text)
    }
}

impl From<String> for Affix {
    fn from(text: String) -> Self {
        Self::parse(text)
    }
}

impl Display for Affix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for run in &self.runs {
            f.write_str(&run.text)?;
        }
        Ok(())
    }
}

/// Apply a tag's formatting on top of the formatting already open.
fn overlay(mut base: Formatting, declared: Formatting) -> Formatting {
    if declared.font_style.is_some() {
        base.font_style = declared.font_style;
    }
    if declared.font_variant.is_some() {
        base.font_variant = declared.font_variant;
    }
    if declared.font_weight.is_some() {
        base.font_weight = declared.font_weight;
    }
    if declared.text_decoration.is_some() {
        base.text_decoration = declared.text_decoration;
    }
    if declared.vertical_align.is_some() {
        base.vertical_align = declared.vertical_align;
    }
    base
}

/// A supported rich-text tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MarkupTag {
    Italic,
    Bold,
    SmallCaps,
    Superscript,
    Subscript,
    /// `<span class="nocase">`: affects text case, not run formatting.
    NoCase,
    /// `<span class="nodecor">`: resets every decoration to its normal value.
    NoDecor,
    /// `<span style="…">`: the declarations of the `style` attribute.
    Styled(Formatting),
    /// `</span>`, matching the innermost span scope of any kind.
    Span,
}

impl MarkupTag {
    /// Parse a tag body (the text between `<` and `>`).
    fn parse(tag: &str) -> Option<(Self, bool)> {
        let tag = tag.trim();
        let (closing, name) = match tag.strip_prefix('/') {
            Some(name) => (true, name),
            None => (false, tag),
        };
        let name = name.trim();
        if name.is_empty() || name.chars().any(|c| c == '/') {
            return None;
        }

        // `span` tags carry their scope in attributes; `</span>` closes the
        // innermost span scope whatever it declared.
        if let Some(rest) = name.strip_prefix("span") {
            if !rest.is_empty() && !rest.chars().next().is_some_and(char::is_whitespace) {
                return None;
            }
            let rest = rest.trim();
            if rest.is_empty() {
                return if closing { Some((Self::Span, true)) } else { None };
            }
            if closing {
                return Some((Self::Span, true));
            }
            if let Some(class) = attribute_value(rest, "class") {
                return match class.trim() {
                    "nocase" => Some((Self::NoCase, false)),
                    "nodecor" => Some((Self::NoDecor, false)),
                    _ => None,
                };
            }
            if let Some(style) = attribute_value(rest, "style") {
                let formatting = parse_css_formatting(style);
                return (!formatting.is_empty())
                    .then_some((Self::Styled(formatting), false));
            }
            return None;
        }

        // Bare tags do not take attributes.
        if name.chars().any(char::is_whitespace) {
            return None;
        }
        let tag = match name.to_ascii_lowercase().as_str() {
            "i" => Self::Italic,
            "b" => Self::Bold,
            "sc" => Self::SmallCaps,
            "sup" => Self::Superscript,
            "sub" => Self::Subscript,
            _ => return None,
        };
        Some((tag, closing))
    }

    /// Whether this open scope is the one a closing tag closes.
    fn matches_close(self, close: Self) -> bool {
        match close {
            // `</span>` closes the innermost span scope, whatever it declared
            // (`nocase`, `nodecor` or a styled span).
            Self::Span => matches!(self, Self::NoCase | Self::NoDecor | Self::Styled(_)),
            _ => self == close,
        }
    }

    /// The formatting this tag declares.
    fn formatting(self) -> citationberg::Formatting {
        let mut formatting = citationberg::Formatting::default();
        match self {
            Self::Italic => formatting.font_style = Some(FontStyle::Italic),
            Self::Bold => formatting.font_weight = Some(FontWeight::Bold),
            Self::SmallCaps => formatting.font_variant = Some(FontVariant::SmallCaps),
            Self::Superscript => formatting.vertical_align = Some(VerticalAlign::Sup),
            Self::Subscript => formatting.vertical_align = Some(VerticalAlign::Sub),
            Self::NoCase => {}
            Self::NoDecor => {
                formatting.font_style = Some(FontStyle::Normal);
                formatting.font_variant = Some(FontVariant::Normal);
                formatting.font_weight = Some(FontWeight::Normal);
                formatting.text_decoration = Some(TextDecoration::None);
            }
            Self::Styled(declared) => formatting = declared,
            Self::Span => {}
        }
        formatting
    }
}

/// Map the CSS declarations citeproc-js accepts in `style` attributes to
/// formatting. Unlike CSL variables, item affixes may carry several
/// declarations in one span (`<span style="font-style:italic;font-weight:bold">`);
/// every recognized declaration is applied, the last one winning per property.
fn parse_css_formatting(style: &str) -> Formatting {
    let mut formatting = Formatting::default();
    for declaration in style.split(';') {
        let Some((property, value)) = declaration.split_once(':') else {
            continue;
        };
        let property = property.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        match (property.as_str(), value.as_str()) {
            ("font-style", "italic" | "oblique") => {
                formatting.font_style = Some(FontStyle::Italic)
            }
            ("font-style", "normal") => formatting.font_style = Some(FontStyle::Normal),
            ("font-variant", "small-caps") => {
                formatting.font_variant = Some(FontVariant::SmallCaps)
            }
            ("font-variant", "normal") => {
                formatting.font_variant = Some(FontVariant::Normal)
            }
            ("font-weight", "bold") => formatting.font_weight = Some(FontWeight::Bold),
            ("font-weight", "normal") => {
                formatting.font_weight = Some(FontWeight::Normal)
            }
            ("text-decoration", "underline") => {
                formatting.text_decoration = Some(TextDecoration::Underline)
            }
            ("text-decoration", "none") => {
                formatting.text_decoration = Some(TextDecoration::None)
            }
            ("vertical-align", "sup" | "super") => {
                formatting.vertical_align = Some(VerticalAlign::Sup)
            }
            ("vertical-align", "sub" | "subscript") => {
                formatting.vertical_align = Some(VerticalAlign::Sub)
            }
            ("vertical-align", "baseline") => {
                formatting.vertical_align = Some(VerticalAlign::Baseline)
            }
            _ => {}
        }
    }
    formatting
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_text_is_one_run() {
        let affix = Affix::parse("See ");
        assert_eq!(affix.as_plain(), "See ");
        assert_eq!(affix.runs().len(), 1);
        assert_eq!(affix.runs()[0].formatting, Formatting::default());
    }

    #[test]
    fn markup_becomes_formatted_runs() {
        let affix = Affix::parse("<sc>See</sc> ");
        let runs = affix.runs();
        assert_eq!(runs.len(), 2);
        assert_eq!(runs[0].text, "See");
        assert_eq!(runs[0].formatting.font_variant, Some(FontVariant::SmallCaps));
        assert_eq!(runs[1].text, " ");
        assert_eq!(affix.as_plain(), "See ");

        let affix = Affix::parse("a <i>b</i> <b>c</b>");
        let runs = affix.runs();
        assert_eq!(runs.len(), 4);
        assert_eq!(runs[1].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[3].formatting.font_weight, Some(FontWeight::Bold));
    }

    #[test]
    fn nested_and_unknown_markup() {
        let affix = Affix::parse("<i>a<sup>b</sup>c</i>");
        let runs = affix.runs();
        assert_eq!(runs.len(), 3);
        assert_eq!(runs[1].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[1].formatting.vertical_align, Some(VerticalAlign::Sup));
        assert_eq!(runs[2].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[2].formatting.vertical_align, None);

        let affix = Affix::parse("a <span>b</span>");
        assert_eq!(affix.as_plain(), "a <span>b</span>");
    }

    #[test]
    fn span_style_declarations_become_runs() {
        let affix = Affix::parse(r#"a <span style="font-style:italic">b</span> c"#);
        let runs = affix.runs();
        assert_eq!(runs.len(), 3);
        assert_eq!(runs[1].text, "b");
        assert_eq!(runs[1].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[2].formatting, Formatting::default());
        assert_eq!(affix.as_plain(), "a b c");
    }

    #[test]
    fn span_style_applies_every_declaration() {
        let affix = Affix::parse(
            r#"<span style="font-style: italic; font-weight:bold; font-variant: small-caps">x</span>"#,
        );
        let run = &affix.runs()[0];
        assert_eq!(run.formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(run.formatting.font_weight, Some(FontWeight::Bold));
        assert_eq!(run.formatting.font_variant, Some(FontVariant::SmallCaps));
    }

    #[test]
    fn span_styles_nest_with_bare_tags() {
        // A styled span inside `<i>` keeps the italic declaration and adds its
        // own; `</span>` restores the italic-only scope.
        let affix = Affix::parse(
            r#"<i>a<span style="font-weight:bold">b<sup>c</sup></span>d</i>e"#,
        );
        let runs = affix.runs();
        assert_eq!(runs.len(), 5);
        assert_eq!(runs[0].text, "a");
        assert_eq!(runs[0].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[1].text, "b");
        assert_eq!(runs[1].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[1].formatting.font_weight, Some(FontWeight::Bold));
        assert_eq!(runs[2].text, "c");
        assert_eq!(runs[2].formatting.vertical_align, Some(VerticalAlign::Sup));
        assert_eq!(runs[2].formatting.font_weight, Some(FontWeight::Bold));
        assert_eq!(runs[3].text, "d");
        assert_eq!(runs[3].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[3].formatting.font_weight, None);
        assert_eq!(runs[4].formatting, Formatting::default());
    }

    #[test]
    fn span_nocase_keeps_formatting_and_closes_at_span() {
        let affix = Affix::parse(r#"<i><span class="nocase">a</span>b</i>"#);
        let runs = affix.runs();
        assert_eq!(runs.len(), 2);
        assert_eq!(runs[0].formatting.font_style, Some(FontStyle::Italic));
        assert_eq!(runs[1].formatting.font_style, Some(FontStyle::Italic));
    }

    #[test]
    fn span_nodecor_resets_decorations() {
        let affix = Affix::parse(r#"<i><span class="nodecor">a</span>b</i>"#);
        let runs = affix.runs();
        assert_eq!(runs.len(), 2);
        assert_eq!(runs[0].formatting.font_style, Some(FontStyle::Normal));
        assert_eq!(runs[0].formatting.font_weight, Some(FontWeight::Normal));
        assert_eq!(runs[0].formatting.text_decoration, Some(TextDecoration::None));
        assert_eq!(runs[1].formatting.font_style, Some(FontStyle::Italic));
    }

    #[test]
    fn unknown_spans_stay_literal() {
        let affix = Affix::parse(r#"a <span class="other">b</span> c"#);
        assert_eq!(affix.as_plain(), r#"a <span class="other">b</span> c"#);
        assert!(affix.runs().iter().all(|run| run.formatting == Formatting::default()));
    }
}
