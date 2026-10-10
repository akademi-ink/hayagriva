//! Smart quotation marks for CSL text.
//!
//! citeproc-js runs a "flip-flop" pass over the rendered citation that turns
//! straight (and typed) quotation marks into the locale's quotation marks.
//! Opening quotes alternate between the outer (`open-quote`) and inner
//! (`open-inner-quote`) forms depending on the current nesting depth; a quote
//! that looks like an apostrophe stays a right single quotation mark. This
//! module provides a small, transactional variant of that pass that is applied
//! to plain text as it is written into the buffer.

use citationberg::TermForm;
use citationberg::taxonomy::OtherTerm;

use super::StyleContext;

/// The quotation marks of a locale.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct QuoteMarks {
    /// The opening outer quotation mark (`open-quote`).
    pub open_quote: String,
    /// The closing outer quotation mark (`close-quote`).
    pub close_quote: String,
    /// The opening inner quotation mark (`open-inner-quote`).
    pub open_inner_quote: String,
    /// The closing inner quotation mark (`close-inner-quote`).
    pub close_inner_quote: String,
}

impl QuoteMarks {
    /// Look the quotation marks up in the style's locale, falling back to
    /// straight quotes when a term is missing.
    pub fn get(style: &StyleContext<'_>) -> Self {
        let term = |term: OtherTerm| {
            style.lookup_locale(|l| {
                l.term(term.into(), TermForm::default())
                    .and_then(|t| t.single())
                    .map(str::to_string)
            })
        };

        Self {
            open_quote: term(OtherTerm::OpenQuote).unwrap_or_else(|| "\"".into()),
            close_quote: term(OtherTerm::CloseQuote).unwrap_or_else(|| "\"".into()),
            open_inner_quote: term(OtherTerm::OpenInnerQuote)
                .unwrap_or_else(|| "'".into()),
            close_inner_quote: term(OtherTerm::CloseInnerQuote)
                .unwrap_or_else(|| "'".into()),
        }
    }

    /// Byte position where a trailing run of closing quotation marks begins,
    /// if any. Marks may consist of multiple characters; the run is scanned
    /// from the end.
    pub fn trailing_close_quote_start(&self, text: &str) -> Option<usize> {
        let mut end = text.len();
        let mut found = false;
        loop {
            let mut matched = false;
            for mark in [&self.close_quote, &self.close_inner_quote] {
                if !mark.is_empty() && text[..end].ends_with(mark.as_str()) {
                    end -= mark.len();
                    found = true;
                    matched = true;
                    break;
                }
            }
            if !matched {
                break;
            }
        }
        found.then_some(end)
    }
}

/// A quotation scope opened by a quotation mark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Scope {
    /// Whether the scope was opened by a double quotation mark.
    family: bool,
    /// Whether the scope was opened by a straight (rather than typed) mark.
    straight: bool,
}

/// Stateful converter that turns straight and typed quotation marks into the
/// locale's quotation marks.
///
/// The converter is transactional per string: opening quotation marks that are
/// not closed within the string are restored to their original characters,
/// like citeproc-js neutralizes unmatched quote tags. This keeps stray quotes
/// (for example `flipflop_OrphanQuote`) untouched.
#[derive(Debug, Clone, Default)]
pub(crate) struct SmartQuoter {
    /// The currently open quote scopes, outermost first.
    scopes: Vec<Scope>,
    /// The family (double or single) of the first straight quote that opened a
    /// scope. Like citeproc-js, the first straight quote form encountered
    /// becomes the outer form; the other family becomes the inner form.
    outer_family: Option<bool>,
}

impl SmartQuoter {
    /// Open a quotation created by a `quotes="true"` element and return its
    /// opening mark.
    pub fn open_quotes<'a>(&mut self, marks: &'a QuoteMarks) -> &'a str {
        let outer = self.open_form(true, false);
        self.scopes.push(Scope { family: true, straight: false });
        if outer { &marks.open_quote } else { &marks.open_inner_quote }
    }

    /// Close the innermost quotation created by a `quotes="true"` element and
    /// return its closing mark.
    pub fn close_quotes<'a>(&mut self, marks: &'a QuoteMarks) -> &'a str {
        let outer = self.close_form();
        if outer { &marks.close_quote } else { &marks.close_inner_quote }
    }

    /// The form (outer vs. inner) of the quotation currently being opened.
    fn open_form(&mut self, family: bool, straight: bool) -> bool {
        if straight && self.outer_family.is_none() {
            self.outer_family = Some(family);
        }

        if self.scopes.is_empty() {
            if straight { self.outer_family.unwrap_or(family) == family } else { family }
        } else {
            self.form_outer_at(self.scopes.len())
        }
    }

    /// The form (outer vs. inner) of the innermost open quotation.
    fn close_form(&self) -> bool {
        self.form_outer_at(self.scopes.len() - 1)
    }

    /// The form (outer vs. inner) of the quotation at `depth`.
    fn form_outer_at(&self, depth: usize) -> bool {
        let base_outer = match self.scopes.first() {
            Some(first) if first.straight => {
                self.outer_family.unwrap_or(first.family) == first.family
            }
            Some(first) => first.family,
            None => true,
        };
        base_outer != (depth % 2 == 1)
    }

    /// Convert the quotation marks in `s`.
    pub fn apply(&mut self, s: &str, marks: &QuoteMarks) -> String {
        if !s.chars().any(is_quote_like) {
            return s.to_string();
        }

        let start_depth = self.scopes.len();
        let mut out = String::with_capacity(s.len() + 8);

        // Opening marks that have not been closed yet, as (byte position in
        // `out`, emitted length, character to restore). They are restored at
        // the end of the string.
        let mut openers: Vec<(usize, usize, char)> = Vec::new();

        let mut chars = s.chars().peekable();
        let mut prev: Option<char> = None;
        while let Some(c) = chars.next() {
            let next = chars.peek().copied();
            match c {
                '"' | '“' => {
                    if c == '“' || is_open_context(prev) {
                        self.open(&mut out, &mut openers, marks, c, true, c == '"');
                    } else if self.scopes.last().is_some_and(|s| s.family) {
                        self.close(&mut out, marks);
                    } else {
                        out.push(c);
                    }
                }
                '\'' | '‘' | '’' => {
                    let apostrophe = matches!(c, '\'' | '’')
                        && prev.is_some_and(char::is_alphanumeric)
                        && next.is_some_and(char::is_alphanumeric);
                    if c == '‘' {
                        self.open(&mut out, &mut openers, marks, c, false, false);
                    } else if apostrophe {
                        // An apostrophe never opens or closes a scope.
                        out.push('’');
                    } else if is_open_context(prev) {
                        self.open(&mut out, &mut openers, marks, c, false, c == '\'');
                    } else if self.scopes.last().is_some_and(|s| !s.family) {
                        self.close(&mut out, marks);
                    } else {
                        out.push(if c == '\'' { '’' } else { c });
                    }
                }
                '”' => {
                    if self.scopes.last().is_some_and(|s| s.family) {
                        self.close(&mut out, marks);
                    } else {
                        out.push(c);
                    }
                }
                _ => out.push(c),
            }
            prev = Some(c);
        }

        // Restore unclosed opening marks and drop their scopes.
        let unclosed = self.scopes.len() - start_depth;
        for (pos, len, restore) in openers.into_iter().rev().take(unclosed) {
            out.replace_range(pos..pos + len, &restore.to_string());
        }
        self.scopes.truncate(start_depth);

        out
    }

    /// Emit an opening mark for `orig`.
    fn open(
        &mut self,
        out: &mut String,
        openers: &mut Vec<(usize, usize, char)>,
        marks: &QuoteMarks,
        orig: char,
        family: bool,
        straight: bool,
    ) {
        let outer = self.open_form(family, straight);
        let mark = if outer { &marks.open_quote } else { &marks.open_inner_quote };
        // Unmatched straight single quotes become apostrophes when restored;
        // unmatched double quotes stay straight (citeproc-js behavior).
        let restore = if orig == '\'' { '’' } else { orig };
        openers.push((out.len(), mark.len(), restore));
        out.push_str(mark);
        self.scopes.push(Scope { family, straight });
    }

    /// Emit a closing mark for the innermost scope.
    fn close(&mut self, out: &mut String, marks: &QuoteMarks) {
        let outer = self.close_form();
        let mark = if outer { &marks.close_quote } else { &marks.close_inner_quote };
        self.scopes.pop();
        out.push_str(mark);
    }
}

/// Whether `c` is a character the quotation pass has to look at.
fn is_quote_like(c: char) -> bool {
    matches!(c, '"' | '\'' | '‘' | '’' | '“' | '”')
}

/// Whether a quotation mark preceded by `prev` opens a new quotation.
fn is_open_context(prev: Option<char>) -> bool {
    prev.is_none_or(|c| c.is_whitespace() || matches!(c, '(' | '[' | '{'))
}

/// Convert the quotation marks in `s` with a fresh quoter.
pub(crate) fn apply(s: &str, marks: &QuoteMarks) -> String {
    SmartQuoter::default().apply(s, marks)
}

/// Move `punct` into a trailing run of closing quotation marks in `text`.
///
/// Returns `true` if the punctuation was inserted, and `false` if it should
/// be suppressed because it duplicates or is dominated by the punctuation
/// that already precedes the closing marks.
pub(crate) fn move_punctuation_inside(
    text: &mut String,
    punct: char,
    marks: &QuoteMarks,
) -> bool {
    let Some(pos) = marks.trailing_close_quote_start(text) else {
        return false;
    };

    let before = text[..pos].chars().next_back();
    let suppress = before == Some(punct)
        || (punct == '.' && matches!(before, Some('?' | '!' | ';' | ':')));
    if !suppress {
        text.insert(pos, punct);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn marks() -> QuoteMarks {
        QuoteMarks {
            open_quote: "“".into(),
            close_quote: "”".into(),
            open_inner_quote: "‘".into(),
            close_inner_quote: "’".into(),
        }
    }

    fn convert(s: &str) -> String {
        apply(s, &marks())
    }

    #[test]
    fn converts_straight_quotes_by_depth() {
        assert_eq!(convert("A \"quote\" here"), "A “quote” here");
        assert_eq!(convert("A 'quote' here"), "A “quote” here");
        assert_eq!(convert("\"outer 'inner' outer\""), "“outer ‘inner’ outer”");
        assert_eq!(convert("\"one\" and \"two\""), "“one” and “two”");
        assert_eq!(convert("rock 'n' roll"), "rock “n” roll");
    }

    #[test]
    fn converts_typed_quotes_by_depth() {
        assert_eq!(convert("My “Amazing” Title"), "My “Amazing” Title");
        assert_eq!(
            convert("‘Parmenides’ and Plato's thought"),
            "‘Parmenides’ and Plato’s thought"
        );
    }

    #[test]
    fn keeps_apostrophes() {
        assert_eq!(convert("Don't Stop"), "Don’t Stop");
        assert_eq!(convert("Shun'ichi"), "Shun’ichi");
        assert_eq!(convert("5'11\" tall"), "5’11\" tall");
        assert_eq!(convert("ETFA '09"), "ETFA ’09");
    }

    #[test]
    fn restores_unmatched_quotes() {
        assert_eq!(
            convert("Nation of \"Positive Obligations \" of State"),
            "Nation of \"Positive Obligations \" of State"
        );
    }

    #[test]
    fn nested_with_attr_quotes() {
        let marks = marks();
        let mut quoter = SmartQuoter::default();
        let open = quoter.open_quotes(&marks).to_string();
        let text = quoter.apply("say \"hi\" to 'her'", &marks);
        let close = quoter.close_quotes(&marks).to_string();
        assert_eq!(format!("{open}{text}{close}"), "“say ‘hi’ to ‘her’”");
    }

    #[test]
    fn trailing_close_quotes() {
        let marks = marks();
        assert_eq!(marks.trailing_close_quote_start("abc”"), Some(3));
        assert_eq!(marks.trailing_close_quote_start("abc’”"), Some(3));
        assert_eq!(marks.trailing_close_quote_start("abc"), None);
    }

    #[test]
    fn deduplicates_moved_punctuation() {
        let marks = marks();
        let mut text = "“Ends ?”".to_string();
        assert!(move_punctuation_inside(&mut text, '.', &marks));
        assert_eq!(text, "“Ends ?”");

        let mut text = "“Ends word”".to_string();
        assert!(move_punctuation_inside(&mut text, '.', &marks));
        assert_eq!(text, "“Ends word.”");
    }
}
