use std::borrow::Cow;
use std::cmp::Ordering;
use std::str::FromStr;

use citationberg::LongShortForm;
use serde::ser::SerializeMap;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use unicode_segmentation::UnicodeSegmentation;

use crate::lang::en::ARTICLES;
use crate::lang::is_cjk;
use crate::lang::name::NAME_PARTICLES;
use crate::util::{deserialize_one_or_many, serialize_one_or_many};

use super::derive_or_from_str;

/// A list of persons with a common role.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct PersonsWithRoles {
    /// The persons.
    #[serde(serialize_with = "serialize_one_or_many")]
    #[serde(deserialize_with = "deserialize_one_or_many")]
    pub names: Vec<Person>,
    /// The role the persons had in the creation of the cited item.
    pub role: PersonRole,
}

impl PersonsWithRoles {
    /// Create a new list of persons with a common role.
    pub fn new(names: Vec<Person>, role: PersonRole) -> Self {
        Self { names, role }
    }
}

/// Specifies the role a group of persons had in the creation to the
/// cited item.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[serde(rename_all = "kebab-case")]
pub enum PersonRole {
    /// Translated the work from a foreign language to the cited edition.
    Translator,
    /// Authored an afterword.
    Afterword,
    /// Authored an foreword.
    Foreword,
    /// Authored an introduction.
    Introduction,
    /// Provided value-adding annotations.
    Annotator,
    /// Commented the work.
    Commentator,
    /// Holds a patent or similar.
    Holder,
    /// Compiled the works in an [Anthology](super::EntryType::Anthology).
    Compiler,
    /// Founded the publication.
    Founder,
    /// Collaborated on the cited item.
    Collaborator,
    /// Organized the creation of the cited item.
    Organizer,
    /// Performed in the cited item.
    CastMember,
    /// Composed all or parts of the cited item's musical / audible components.
    Composer,
    /// Produced the cited item.
    Producer,
    /// Lead Producer for the cited item.
    ExecutiveProducer,
    /// Did the writing for the cited item.
    Writer,
    /// Shot film/video for the cited item.
    Cinematography,
    /// Directed the cited item.
    Director,
    /// Illustrated the cited item.
    Illustrator,
    /// Provided narration or voice-over for the cited item.
    Narrator,

    /// Various other roles described by the contained string.
    #[serde(skip)]
    Unknown(String),
}

derive_or_from_str! {
    /// Holds the name of a person.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub struct Person where "a name string or a dictionary with a \"name\" key" {
        /// The family name.
        pub name: String,
        /// The given name / forename.
        pub given_name: Option<String>,
        /// A prefix of the family name such as 'van' or 'de'.
        pub prefix: Option<String>,
        /// A suffix of the family name such as 'Jr.' or 'IV'.
        pub suffix: Option<String>,
        /// Whether a comma should be inserted before the suffix.
        #[serde(default)]
        pub comma_suffix: bool,
        /// Another name (often user name) the person might be known under.
        pub alias: Option<String>,
        /// Whether the family name arrived quoted (`"van Happel"`): citeproc
        /// treats it verbatim and does not split an implicit particle.
        #[serde(default)]
        pub literal_family: bool,
        /// An explicit CSL-JSON `non-dropping-particle`. Kept separately from
        /// the family name so that sort decisions do not have to guess.
        pub non_dropping_particle: Option<String>,
    }
}

impl Serialize for Person {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // Aliases are not represented in the string, prefixes can create
        // ambiguity.
        if self.alias.is_none() && self.prefix.is_none() {
            serializer.serialize_str(&self.name_first(false, false))
        } else {
            let entries = [
                ("name", Some(&self.name)),
                ("given-name", self.given_name.as_ref()),
                ("prefix", self.prefix.as_ref()),
                ("suffix", self.suffix.as_ref()),
                ("alias", self.alias.as_ref()),
            ];

            let map_len = entries.iter().filter(|(_, v)| v.is_some()).count();

            let mut map = serializer.serialize_map(Some(map_len))?;

            for (key, value) in entries.iter() {
                if let Some(value) = value {
                    map.serialize_entry(key, value)?;
                }
            }

            map.end()
        }
    }
}

/// Error that may occur when parsing a slice of strings as a name.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum PersonError {
    /// The name has too many parts to be appropriately parsed.
    #[error("too many parts")]
    TooManyParts,
    /// The name is empty.
    #[error("part list is empty")]
    Empty,
    /// The role is unknown.
    #[error("unknown role")]
    UnknownRole,
}

fn split_implicit_particle(name: String) -> (String, Option<String>) {
    for (idx, ch) in name.char_indices().rev() {
        if ch != ' ' {
            continue;
        }
        let particle = &name[..idx];
        if NAME_PARTICLES
            .binary_search(&particle.to_lowercase().as_str())
            .is_ok()
        {
            return (name[idx + 1..].to_string(), Some(particle.to_string()));
        }
    }
    (name, None)
}

impl Person {
    /// This function expects a list of strings with its length between one and
    /// three. The first part will be interpreted as the `<prefix> <Name>`, the
    /// second part as the given name and the third part as the suffix.
    ///
    /// The prefix and name are separated just like in BiBTeX, as described
    /// [Nicolas Markey describes in "Tame the BeaST"][taming], p. 24. The gist
    /// is that the given name will start at the first word with a capital
    /// letter, if there are any such words.
    ///
    /// The call site of this function in the library obtains the slice by
    /// calling `split(",")` on a string like `"Des Egdens, Britta"`.
    ///
    /// [taming]: https://mirrors.ctan.org/info/bibtex/tamethebeast/ttb_en.pdf#section.11
    pub fn from_strings(mut parts: Vec<&str>) -> Result<Self, PersonError> {
        if parts.is_empty() {
            return Err(PersonError::Empty);
        } else if parts.len() > 3 {
            return Err(PersonError::TooManyParts);
        }

        for part in parts.iter_mut() {
            *part = part.trim();
        }

        let last_pre = parts[0];
        let given_name = (parts.len() > 1)
            .then(|| parts.last().map(|last| last.to_string()))
            .flatten();

        let suffix = if parts.len() > 2 { Some(parts[1].to_string()) } else { None };

        let mut word_start = true;
        let mut last_lower_case_end: i32 = -1;
        let mut is_lowercase = false;
        let mut last_word_start = 0;
        let mut has_seen_uppercase_words = false;

        for (index, c) in last_pre.chars().enumerate() {
            if c.is_whitespace() {
                word_start = true;
                continue;
            }

            if word_start {
                last_word_start = index;

                if c.is_lowercase() {
                    is_lowercase = true;
                } else {
                    is_lowercase = false;
                    has_seen_uppercase_words = true;
                }
            }

            if is_lowercase {
                last_lower_case_end = index as i32;
            }

            word_start = false;
        }

        let mut name = String::new();
        let mut prefix = String::new();
        for (index, c) in last_pre.chars().enumerate() {
            if (index as i32 <= last_lower_case_end && has_seen_uppercase_words)
                || (!has_seen_uppercase_words && index < last_word_start)
            {
                prefix.push(c);
            } else if has_seen_uppercase_words || index >= last_word_start {
                name.push(c);
            }
        }

        let prefix = if prefix.is_empty() { None } else { Some(prefix) };
        if prefix.is_some() {
            name = name.trim_start().to_string();
        }

        // BibTeX family strings may carry an implicit non-dropping particle
        // with any capitalization; keep that behavior for this parser only.
        let (name, particle) = split_implicit_particle(name);
        Ok(Person {
            name,
            given_name,
            prefix,
            suffix,
            comma_suffix: false,
            alias: None,
            literal_family: false,
            non_dropping_particle: particle,
        })
    }

    /// Formats the given name into initials.
    ///
    /// This follows citeproc-js's `CSL.Util.Names.initializeWith` with
    /// `initialize="true"`: the given name is split into initials and
    /// abbreviations, lower-case name particles are kept in full, and the
    /// `delimiter` (the style's `initialize-with` value) is placed after every
    /// initial.
    ///
    /// For example, `"Judith Beatrice"` yields `"J. B."` for a delimiter of
    /// `Some(". ")` and `"Klaus-Peter"` becomes `"K.-P."` when hyphens are
    /// kept (`with_hyphen`), or `"K. P."` when they are treated as spaces.
    ///
    /// Existing periods in the input are interpreted as initial separators
    /// (`"M.E"` is two initials), so abbreviations like `"Ph."` and long
    /// abbreviations such as `"TSerendorjiin"` are handled like citeproc-js.
    pub fn initials(
        &self,
        buf: &mut impl std::fmt::Write,
        delimiter: Option<&str>,
        with_hyphen: bool,
    ) -> std::fmt::Result {
        let Some(gn) = &self.given_name else {
            return Ok(());
        };

        buf.write_str(&initialize_given_name(
            gn,
            delimiter.unwrap_or_default(),
            with_hyphen,
            false,
        ))
    }

    /// Normalizes existing initials in the given name without initializing
    /// full words (`initialize="false"` with `initialize-with` set).
    ///
    /// citeproc-js still parses the given name into initials and abbreviations
    /// and rewrites their separators according to `delimiter`.
    pub fn normalize_initials(
        &self,
        buf: &mut impl std::fmt::Write,
        delimiter: Option<&str>,
        with_hyphen: bool,
    ) -> std::fmt::Result {
        let Some(gn) = &self.given_name else {
            return Ok(());
        };

        buf.write_str(&initialize_given_name(
            gn,
            delimiter.unwrap_or_default(),
            with_hyphen,
            true,
        ))
    }

    /// Yields the first name of a person. Will add the delimiter after initials
    /// / single letters.
    pub fn first_name_with_delimiter(
        &self,
        buf: &mut impl std::fmt::Write,
        delimiter: Option<&str>,
    ) -> std::fmt::Result {
        let Some(name) = &self.given_name else {
            return Ok(());
        };

        let mut first = true;
        for item in name.split(' ') {
            if !first {
                buf.write_char(' ')?;
            }

            buf.write_str(item)?;

            if let Some(delimiter) = delimiter
                && item.graphemes(true).count() == 1
            {
                buf.write_str(delimiter)?;
            }

            first = false;
        }

        Ok(())
    }

    /// Get the name with the family name first, the initials
    /// afterwards, separated by a comma.
    pub fn name_first(&self, initials: bool, prefix_given_name: bool) -> String {
        let mut res = if !prefix_given_name {
            if let Some(prefix) = &self.prefix {
                format!("{} {}", prefix, self.name)
            } else {
                self.name.clone()
            }
        } else {
            self.name.clone()
        };

        if initials {
            if self.given_name.is_some() {
                res += ", ";
                self.initials(&mut res, Some(". "), true).unwrap();
            }
        } else if let Some(given_name) = &self.given_name {
            res += ", ";
            res += given_name;
        }

        if prefix_given_name && let Some(prefix) = &self.prefix {
            if self.given_name.is_some() {
                res.push(' ');
            }

            res += prefix;
        }

        if let Some(suffix) = &self.suffix {
            res += ", ";
            res += suffix;
        }
        res
    }

    /// Get the name with the given name first, the family name afterwards.
    pub fn given_first(&self, initials: bool) -> String {
        let mut res = String::new();

        if initials {
            if self.given_name.is_some() {
                self.initials(&mut res, Some(". "), true).unwrap();
                res.push(' ');
            }
        } else if let Some(given_name) = &self.given_name {
            res += given_name;
            res.push(' ');
        }

        if let Some(prefix) = &self.prefix {
            res += prefix;
            res += " ";
        }

        res += &self.name;

        if let Some(suffix) = &self.suffix {
            res += " ";
            res += suffix;
        }

        res
    }

    /// Get the non-dropping name particle in the family name.
    pub fn name_particle(&self) -> Option<&str> {
        if let Some(particle) = &self.non_dropping_particle {
            return Some(particle);
        }
        if self.literal_family {
            return None;
        }
        // Only a lower-case leading word is an implicit particle:
        // "van Gogh" is, "De Quincey" is not (citeproc-js's own name parser
        // keys on case).
        for (idx, char) in self.name.char_indices().rev() {
            if char != ' ' {
                continue;
            }

            let particle = &self.name[0..idx];
            if !particle.starts_with(|c: char| c.is_lowercase()) {
                continue;
            }
            let lowercase = particle.to_lowercase();
            if NAME_PARTICLES.binary_search(&lowercase.as_str()).is_ok() {
                return Some(particle);
            }
        }

        // Hyphenated particles: `al-One` -> particle `al-`, family `One`.
        if let Some(idx) = self.name.rfind('-') {
            let particle = &self.name[..=idx];
            let base = &self.name[..idx];
            if particle.starts_with(|c: char| c.is_lowercase())
                && NAME_PARTICLES.binary_search(&base.to_lowercase().as_str()).is_ok()
            {
                return Some(particle);
            }
        }

        None
    }

    /// Get the family name without the non-dropping particle.
    pub fn name_without_particle(&self) -> &str {
        if self.non_dropping_particle.is_some() {
            self.name.as_str()
        } else if let Some(particle) = self.name_particle() {
            self.name[particle.len()..].trim_start()
        } else {
            self.name.as_str()
        }
    }

    /// The particle as it must be printed (explicit particle, if any,
    /// otherwise the implicit prefix retained in the family string).
    pub fn display_particle(&self) -> Option<Cow<'_, str>> {
        if let Some(particle) = &self.non_dropping_particle {
            return Some(Cow::Borrowed(particle.as_str()));
        }
        self.name_particle().map(Cow::Borrowed)
    }

    /// Get only the dropping and non-dropping particle of the family name.
    pub fn name_particles(&self) -> Option<Cow<'_, str>> {
        match (&self.prefix, self.display_particle()) {
            (Some(dropping), Some(non_dropping)) => {
                Some(Cow::Owned(format!("{dropping} {non_dropping}")))
            }
            (Some(dropping), None) => Some(Cow::Borrowed(dropping.as_str())),
            (None, Some(non_dropping)) => Some(non_dropping),
            (None, None) => None,
        }
    }

    /// Whether to treat this as an institutional name.
    pub fn is_institutional(&self) -> bool {
        self.given_name.is_none() && self.suffix.is_none() && self.prefix.is_none()
    }

    /// Whether the name contains CJK characters.
    pub fn is_cjk(&self) -> bool {
        self.name.chars().any(is_cjk)
            || self.given_name.as_ref().is_some_and(|gn| gn.chars().any(is_cjk))
    }

    /// Get the name without the leading article.
    pub fn name_without_article(&self) -> &str {
        let space_idx = self.name.find(' ');
        if let Some(space_idx) = space_idx {
            if space_idx + 1 != self.name.len()
                && ARTICLES.binary_search(&&self.name[0..space_idx]).is_ok()
            {
                &self.name[space_idx + 1..]
            } else {
                self.name.as_str()
            }
        } else {
            self.name.as_str()
        }
    }

    /// Order according to the CSL specification.
    pub(crate) fn csl_cmp(
        &self,
        other: &Self,
        form: LongShortForm,
        demote_particle: bool,
    ) -> std::cmp::Ordering {
        let self_cjk = self.is_cjk();
        let other_cjk = other.is_cjk();

        let name_a = self.name.to_lowercase();
        let name_b = other.name.to_lowercase();
        let given_a = self.given_name.as_ref().map(|s| s.to_lowercase());
        let given_b = other.given_name.as_ref().map(|s| s.to_lowercase());

        if self_cjk != other_cjk {
            // Put CJK names last.
            return self_cjk.cmp(&other_cjk);
        } else if self_cjk && other_cjk {
            // Apply special CJK rules.
            return match form {
                LongShortForm::Long => {
                    name_a.cmp(&name_b).then_with(|| given_a.cmp(&given_b))
                }
                LongShortForm::Short => name_a.cmp(&name_b),
            };
        }

        let prefix_a = self.prefix.as_ref().map(|s| s.to_lowercase());
        let prefix_b = other.prefix.as_ref().map(|s| s.to_lowercase());
        let suffix_a = self.suffix.as_ref().map(|s| s.to_lowercase());
        let suffix_b = other.suffix.as_ref().map(|s| s.to_lowercase());

        if demote_particle {
            self.name_without_particle()
                .to_lowercase()
                .cmp(&other.name_without_particle().to_lowercase())
                .then_with(|| {
                    self.name_particles()
                        .map(|c| c.to_lowercase())
                        .cmp(&other.name_particles().map(|c| c.to_lowercase()))
                })
                .then_with(|| given_a.cmp(&given_b))
                .then_with(|| suffix_a.cmp(&suffix_b))
        } else {
            name_a
                .cmp(&name_b)
                .then_with(|| prefix_a.cmp(&prefix_b))
                .then_with(|| given_a.cmp(&given_b))
                .then_with(|| suffix_a.cmp(&suffix_b))
        }
    }
}

impl Ord for Person {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name
            .cmp(&other.name)
            .then(self.given_name.cmp(&other.given_name))
            .then(self.suffix.cmp(&other.suffix))
            .then(self.prefix.cmp(&other.prefix))
    }
}

impl PartialOrd for Person {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl FromStr for Person {
    type Err = PersonError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_strings(s.split(',').collect())
    }
}

/// The result of splitting a given name like citeproc-js's `nameDoppel`:
/// alternating name fragments and separators (whitespace, hyphens, and the
/// rich-text tags citeproc-js understands).
struct NameChunks {
    strings: Vec<String>,
    tags: Vec<String>,
}

/// Length in bytes of a rich-text tag that citeproc-js treats as a name
/// separator, if `s` starts with one.
///
/// Mirrors the tag alternatives of citeproc-js's `rexNameStr`:
/// `<i>`, `<b>`, `<sc>`, `<sub>`, `<sup>` (and their closing forms) plus the
/// opening `<span class="nocase">` / `<span class="nodecor">` forms and any
/// `</span>`.
fn markup_tag_len(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.first() != Some(&b'<') {
        return None;
    }

    let mut i = 1;
    if bytes.get(i) == Some(&b'/') {
        i += 1;
    }

    const TAGS: [&str; 7] =
        ["span class=\"nocase\"", "span class=\"nodecor\"", "i", "sc", "b", "sub", "sup"];

    for tag in TAGS {
        // A closing `</span>` carries no class attribute.
        if tag.starts_with("span ") && bytes.get(1) == Some(&b'/') {
            if s[i..].starts_with("span") && s.as_bytes().get(i + 4) == Some(&b'>') {
                return Some(i + 5);
            }
            continue;
        }

        if s[i..].starts_with(tag) {
            let end = i + tag.len();
            if s.as_bytes().get(end) == Some(&b'>') {
                return Some(end + 1);
            }
        }
    }

    None
}

fn is_separator_char(c: char) -> bool {
    c == '-' || c.is_whitespace()
}

/// Match a name separator at the start of `s`: an optional run of hyphens and
/// whitespace around a rich-text tag, or a run of hyphens and whitespace.
fn match_name_separator(s: &str) -> Option<(String, usize)> {
    let mut i = 0;
    while let Some(c) = s[i..].chars().next() {
        if is_separator_char(c) {
            i += c.len_utf8();
        } else {
            break;
        }
    }

    if let Some(tag_len) = markup_tag_len(&s[i..]) {
        let mut j = i + tag_len;
        while let Some(c) = s[j..].chars().next() {
            if is_separator_char(c) {
                j += c.len_utf8();
            } else {
                break;
            }
        }
        return Some((s[..j].to_string(), j));
    }

    (i > 0).then(|| (s[..i].to_string(), i))
}

fn split_name_chunks(name: &str) -> NameChunks {
    let mut strings = Vec::new();
    let mut tags = Vec::new();
    let mut current = String::new();
    let mut rest = name;

    while !rest.is_empty() {
        if let Some((separator, len)) = match_name_separator(rest) {
            strings.push(std::mem::take(&mut current));
            tags.push(separator);
            rest = &rest[len..];
        } else {
            let c = rest.chars().next().unwrap();
            current.push(c);
            rest = &rest[c.len_utf8()..];
        }
    }
    strings.push(current);

    NameChunks { strings, tags }
}

/// Strip leading rich-text tags (`/^(?:<[^>]+>)*/`).
fn strip_leading_tags(s: &str) -> &str {
    let mut rest = s;
    while rest.starts_with('<') {
        match rest.find('>') {
            Some(end) => rest = &rest[end + 1..],
            None => break,
        }
    }
    rest
}

/// Return only the rich-text tags in `s`, or `s` itself when it has none
/// (citeproc-js's `tagonly`).
fn tags_only(s: &str) -> String {
    let Some(first) = s.find('<') else {
        return s.to_string();
    };

    let mut i = first;
    let mut out = String::new();
    while s.as_bytes().get(i) == Some(&b'<') {
        match s[i..].find('>') {
            Some(end) => {
                out.push_str(&s[i..i + end + 1]);
                i += end + 1;
            }
            None => break,
        }
    }

    if out.is_empty() { s.to_string() } else { out }
}

/// Merge the tags of `tagstr` into `newstr`, keeping whitespace at the end of
/// `newstr` (citeproc-js's `mergetag`).
fn merge_tags(tagstr: &str, newstr: &str) -> String {
    let mut tags = String::new();
    let bytes = tagstr.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i] == b'<' {
            // Include hyphens that directly precede the tag.
            let mut start = i;
            while start > 0 && bytes[start - 1] == b'-' {
                start -= 1;
            }
            if let Some(end) = tagstr[i..].find('>') {
                let mut end = i + end + 1;
                while tagstr.as_bytes().get(end) == Some(&b'-') {
                    end += 1;
                }
                tags.push_str(&tagstr[start..end]);
                i = end;
                continue;
            }
        }
        i += 1;
    }

    if tags.is_empty() {
        return newstr.to_string();
    }

    let trimmed = newstr.trim_end_matches(char::is_whitespace).len();
    if trimmed < newstr.len() {
        format!("{}{}{}", &newstr[..trimmed], tags, &newstr[trimmed..])
    } else {
        format!("{newstr}{tags}")
    }
}

fn is_initial_start(c: char) -> bool {
    c.is_ascii_uppercase()
        || matches!(c as u32,
            0x0e01..=0x0e5b
            | 0x00c0..=0x017f
            | 0x0400..=0x042f
            | 0x0590..=0x05d4
            | 0x05d6..=0x05ff
            | 0x0600..=0x06ff
            | 0x0370
            | 0x0372
            | 0x0376
            | 0x0386
            | 0x0388..=0x03ab
            | 0x03e2
            | 0x03e4
            | 0x03e6
            | 0x03e8
            | 0x03ea
            | 0x03ec
            | 0x03ee
            | 0x03f4
            | 0x03f7
            | 0x03fd..=0x03ff)
}

fn is_initial_cont(c: char) -> bool {
    c.is_ascii_alphabetic()
        || matches!(c as u32,
            0x0e01..=0x0e5b
            | 0x00c0..=0x017f
            | 0x0400..=0x052f
            | 0x0600..=0x06ff
            | 0x0370..=0x03ff
            | 0x1f00..=0x1fff)
}

fn starts_with_romanesque(s: &str) -> bool {
    s.chars().next().is_some_and(|c| {
        c == '&'
            || c.is_ascii_alphabetic()
            || matches!(c as u32,
                0x0e01..=0x0e5b
                | 0x00c0..=0x017f
                | 0x0370..=0x03ff
                | 0x0400..=0x052f
                | 0x0590..=0x05d4
                | 0x05d6..=0x05ff
                | 0x1f00..=0x1fff
                | 0x0600..=0x06ff
                | 0x200c..=0x200e
                | 0x0218..=0x021b
                | 0x202a..=0x202e)
    })
}

/// citeproc-js's `NAME_INITIAL_REGEXP`: an initial character, a run of
/// letters, and a run of periods.
fn match_initial(n: &str) -> Option<(String, String, String)> {
    let mut chars = n.char_indices();
    let (_, first) = chars.next()?;
    if !is_initial_start(first) {
        return None;
    }

    let mut m1 = first.to_string();
    let mut m2 = String::new();
    let mut m3 = String::new();
    let mut rest = &n[first.len_utf8()..];

    for c in rest.chars() {
        if is_initial_cont(c) {
            m2.push(c);
        } else {
            break;
        }
    }
    rest = &rest[m2.len()..];
    for c in rest.chars() {
        if c == '.' {
            m3.push(c);
        } else {
            break;
        }
    }

    // `m[1] = m[1] + m[2]; m[2] = ""` for abbreviations with a period.
    if !m2.is_empty() && !m3.is_empty() {
        m1.push_str(&m2);
        m2.clear();
    }

    Some((m1, m2, m3))
}

/// Collapse whitespace and hyphens around hyphens (`/\s*\-\s*/g` → `-`).
fn normalize_hyphen_spacing(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    let mut pending_space = false;

    while !rest.is_empty() {
        let c = rest.chars().next().unwrap();
        rest = &rest[c.len_utf8()..];
        if c.is_whitespace() {
            pending_space = true;
            continue;
        }
        if c == '-' && !out.is_empty() {
            while out.ends_with(char::is_whitespace) {
                out.pop();
            }
            out.push('-');
            pending_space = false;
            // Skip whitespace that follows the hyphen.
            let skipped = rest.len() - rest.trim_start_matches(char::is_whitespace).len();
            rest = &rest[skipped..];
            continue;
        }
        if pending_space && !out.is_empty() {
            out.push(' ');
        }
        pending_space = false;
        out.push(c);
    }

    out
}

/// Lower-case letters after a hyphen (temporarily marked with an en dash so
/// the hyphen does not read as a name separator).
fn hyphen_lowercase_to_en_dash(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '-'
            && let Some(&next) = chars.peek()
            && next.is_ascii_lowercase()
        {
            out.push('\u{2013}');
        } else {
            out.push(c);
        }
    }
    out
}

fn collapse_whitespace(s: &str) -> String {
    let mut out = String::new();
    let mut in_space = false;
    for c in s.chars() {
        if c.is_whitespace() {
            in_space = true;
        } else {
            if in_space && !out.is_empty() {
                out.push(' ');
            }
            in_space = false;
            out.push(c);
        }
    }
    out
}

/// citeproc-js's `doNormalize`: rewrite separators between existing initials
/// and abbreviations according to `terminator`.
fn normalize_name_list(namelist: &mut [String], terminator: &str) {
    let mut is_abbrev = Vec::with_capacity(namelist.len());
    for item in namelist.iter_mut() {
        let without_tags = strip_leading_tags(item);
        let bytes = without_tags.as_bytes();
        if without_tags.len() > 1 && without_tags.ends_with('.') {
            // Strip the last period (citeproc-js keeps the tags in place).
            if let Some(pos) = item.rfind('.') {
                item.remove(pos);
            }
            is_abbrev.push(true);
        } else if item.chars().count() == 1
            && item.chars().next().is_some_and(char::is_uppercase)
        {
            is_abbrev.push(true);
        } else if bytes.len() == 1 && bytes[0].is_ascii_uppercase() {
            is_abbrev.push(true);
        } else {
            is_abbrev.push(false);
        }
    }

    let len = namelist.len();
    let mut i = 0;
    while i < len {
        if is_abbrev[i] {
            if i + 2 < len {
                namelist[i + 1] = tags_only(&namelist[i + 1]);
                if !is_abbrev[i + 2] {
                    namelist[i + 1] = format!("{} ", tags_only(&namelist[i + 1]));
                }

                let terminator = terminator.trim_end_matches('\u{feff}');
                if namelist[i + 2].len() > 1 {
                    namelist[i + 1] = format!("{terminator}{}", namelist[i + 1]);
                } else {
                    namelist[i + 1] = merge_tags(&namelist[i + 1], terminator);
                }
            }
            if i + 1 == len {
                namelist[i].push_str(terminator);
            }
        }
        i += 2;
    }
}

/// citeproc-js's `doInitialize`: replace every name fragment with its initial.
fn initialize_name_list(namelist: &mut Vec<String>, terminator: &str) {
    let len = namelist.len();
    let mut i = 0;
    while i < len {
        let n = namelist[i].clone();
        if n.is_empty() {
            i += 2;
            continue;
        }

        let mut m = match_initial(&n);
        if m.is_none()
            && !starts_with_romanesque(&n)
            && n.len() > 1
            && terminator.contains("%s")
        {
            let mut chars = n.chars();
            let first = chars.next().unwrap();
            m = Some((first.to_string(), chars.collect(), String::new()));
        }

        if let Some((m1, m2, m3)) = m {
            if m1.chars().next().is_some_and(char::is_uppercase) {
                let mut extra = String::new();
                if !m2.is_empty() {
                    let upper: String =
                        m2.chars().take_while(|c| c.is_uppercase()).collect();
                    if upper.len() < m2.len() {
                        extra = upper.to_lowercase();
                    }
                }

                namelist[i] = format!("{m1}{extra}");
                if i + 1 < len {
                    if terminator.contains("%s") {
                        namelist[i] = terminator.replace("%s", &namelist[i]);
                    } else if namelist[i + 1].contains('-') {
                        namelist[i + 1] = format!(
                            "{}-",
                            merge_tags(&namelist[i + 1].replace('-', ""), terminator)
                        );
                    } else {
                        namelist[i + 1] = merge_tags(&namelist[i + 1], terminator);
                    }
                } else if terminator.contains("%s") {
                    namelist[i] = terminator.replace("%s", &namelist[i]);
                } else {
                    namelist.push(terminator.to_string());
                }
            } else if starts_with_romanesque(&n) && m3.is_empty() {
                namelist[i] = format!(" {n}");
            }
        } else if starts_with_romanesque(&n) {
            namelist[i] = format!(" {n}");
        }

        i += 2;
    }
}

fn restore_hyphens(s: String) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\u{2013}' && chars.peek().is_some_and(|c| c.is_ascii_lowercase()) {
            out.push('-');
        } else {
            out.push(c);
        }
    }
    out
}

fn finish_name_list(namelist: &[String]) -> String {
    let joined = namelist.join("");
    let trimmed = joined.trim_end_matches(|c: char| {
        matches!(
            c,
            '\t' | '\n' | '\u{000b}' | '\u{000c}' | '\r' | ' ' | '\u{feff}' | '\u{a0}'
        )
    });

    // Normalize hyphens and compress ASCII whitespace, like citeproc-js.
    let mut out = String::with_capacity(trimmed.len());
    let mut chars = trimmed.chars().peekable();
    while let Some(c) = chars.next() {
        if c.is_whitespace() {
            // `\s*-\s*` -> `-`
            let mut lookahead = chars.clone();
            let mut saw_hyphen = false;
            while let Some(&next) = lookahead.peek() {
                if next == '-' {
                    saw_hyphen = true;
                    break;
                }
                if next.is_whitespace() {
                    lookahead.next();
                } else {
                    break;
                }
            }
            if saw_hyphen {
                while let Some(&next) = chars.peek() {
                    if next.is_whitespace() || next == '-' {
                        chars.next();
                        if next == '-' {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                out.push('-');
                continue;
            }

            if !out.ends_with(' ') && !out.is_empty() {
                out.push(' ');
            }
            while chars.peek().is_some_and(|c| c.is_whitespace() && *c != '\u{a0}') {
                chars.next();
            }
        } else {
            out.push(c);
        }
    }

    restore_hyphens(out)
}

fn initialize_given_name(
    name: &str,
    terminator: &str,
    with_hyphen: bool,
    normalize_only: bool,
) -> String {
    if name.is_empty() {
        return String::new();
    }

    if ["Lord", "Lady"].contains(&name)
        || (!starts_with_romanesque(strip_leading_tags(name))
            && !terminator.contains("%s"))
    {
        return name.to_string();
    }

    let mut name = if with_hyphen { name.to_string() } else { name.replace('-', " ") };

    name = normalize_hyphen_spacing(&collapse_whitespace(&name));
    name = hyphen_lowercase_to_en_dash(&name);

    // Insert a space after every period that is not already followed by one.
    let mut spaced = String::with_capacity(name.len() + 4);
    let mut chars = name.chars().peekable();
    while let Some(c) = chars.next() {
        spaced.push(c);
        if c == '.'
            && let Some(&next) = chars.peek()
            && next != ' '
        {
            spaced.push(' ');
        }
    }

    let mut chunks = split_name_chunks(&spaced);
    if chunks.tags.is_empty() {
        let only = &chunks.strings[0];
        if let Some(last) = only.rsplit('.').next()
            && last.chars().count() == 1
            && last.chars().next().is_some_and(char::is_uppercase)
        {
            chunks.strings[0].push('.');
        }
    }

    let mut namelist = vec![chunks.strings[0].clone()];
    for i in 1..chunks.strings.len() {
        namelist.push(chunks.tags[i - 1].clone());
        namelist.push(chunks.strings[i].clone());
    }

    if normalize_only {
        normalize_name_list(&mut namelist, terminator);
    } else {
        initialize_name_list(&mut namelist, terminator);
    }

    finish_name_list(&namelist)
}

#[cfg(test)]
mod tests {
    use super::Person;

    #[test]
    fn person_initials() {
        let mut s = String::new();
        let p = Person::from_strings(vec!["Dissmer", "Courtney Deliah"]).unwrap();
        p.initials(&mut s, Some("."), true).unwrap();
        assert_eq!("C.D.", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Dissmer", "Courtney Deliah"]).unwrap();
        p.initials(&mut s, Some(". "), true).unwrap();
        assert_eq!("C. D.", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Dissmer", "Courtney Deliah"]).unwrap();
        p.initials(&mut s, Some(""), true).unwrap();
        assert_eq!("CD", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Dissmer", "Courtney Deliah"]).unwrap();
        p.initials(&mut s, None, true).unwrap();
        assert_eq!("CD", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, Some(". "), true).unwrap();
        assert_eq!("H.-J.", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, Some("."), true).unwrap();
        assert_eq!("H.-J.", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, Some(""), true).unwrap();
        assert_eq!("H-J", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, None, true).unwrap();
        assert_eq!("H-J", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, Some(". "), false).unwrap();
        assert_eq!("H. J.", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, Some("."), false).unwrap();
        assert_eq!("H.J.", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, Some(""), false).unwrap();
        assert_eq!("HJ", s);

        let mut s = String::new();
        let p = Person::from_strings(vec!["Günther", "Hans-Joseph"]).unwrap();
        p.initials(&mut s, None, false).unwrap();
        assert_eq!("HJ", s);
    }

    #[test]
    fn person_non_dropping_initials() {
        let p = Person::from_strings(vec!["Von Der Leyen", "Ursula"]).unwrap();
        assert_eq!("Von Der", p.name_particle().unwrap());
        assert_eq!("Leyen", p.name_without_particle());
    }
    #[test]
    fn person_middle_initial() {
        let p = Person::from_strings(vec!["Kirk", "James T"]).unwrap();
        let mut s = String::new();
        p.first_name_with_delimiter(&mut s, Some(".")).unwrap();
        assert_eq!("James T.", s);
    }

    #[test]
    fn person_name_retrieval_order() {
        let p =
            Person::from_strings(vec!["van Dissmer", "Jr.", "Courtney Deliah"]).unwrap();
        assert_eq!("van Dissmer, Courtney Deliah, Jr.", p.name_first(false, false));
        assert_eq!("Dissmer, Courtney Deliah van, Jr.", p.name_first(false, true));
        assert_eq!("van Dissmer, C. D., Jr.", p.name_first(true, false));
        assert_eq!("Dissmer, C. D. van, Jr.", p.name_first(true, true));
        assert_eq!("Courtney Deliah van Dissmer Jr.", p.given_first(false));
        assert_eq!("C. D. van Dissmer Jr.", p.given_first(true));
    }
}
