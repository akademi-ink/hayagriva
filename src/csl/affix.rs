//! Rich-text citation-item affixes.
//!
//! citeproc-js parses a small HTML subset in per-item `prefix`/`suffix`
//! values (`<i>`, `<b>`, `<sc>`, `<sup>`, `<sub>`) and splices the resulting
//! formatted runs into the citation. [`Affix`] carries those runs; a plain
//! string remains a single unformatted run so existing callers keep working.

use std::fmt::{self, Display};

use citationberg::{FontStyle, FontVariant, FontWeight, Formatting, VerticalAlign};

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
    /// `<sup>` (superscript) and `<sub>` (subscript), including nesting and
    /// closing tags. Unrecognized tags stay in the text verbatim.
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
                if let Some(pos) = stack.iter().rposition(|(open, _)| *open == tag) {
                    formatting = stack[pos].1;
                    stack.truncate(pos);
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
        if name.is_empty() || name.chars().any(|c| c.is_whitespace() || c == '/') {
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

    /// The formatting this tag declares.
    fn formatting(self) -> citationberg::Formatting {
        let mut formatting = citationberg::Formatting::default();
        match self {
            Self::Italic => formatting.font_style = Some(FontStyle::Italic),
            Self::Bold => formatting.font_weight = Some(FontWeight::Bold),
            Self::SmallCaps => formatting.font_variant = Some(FontVariant::SmallCaps),
            Self::Superscript => formatting.vertical_align = Some(VerticalAlign::Sup),
            Self::Subscript => formatting.vertical_align = Some(VerticalAlign::Sub),
        }
        formatting
    }
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
}
