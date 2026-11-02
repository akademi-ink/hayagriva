use std::borrow::Cow;
use std::cmp;
use std::str::FromStr;

use crate::types::{
    ChunkedString, Date, EntryType, MaybeTyped, Numeric, Person, PersonRole, Publisher,
    StringChunk,
};
use crate::{Entry, PageRanges};
use citationberg::taxonomy::{
    DateVariable, Kind, NameVariable, NumberVariable, PageVariable, StandardVariable,
};
use citationberg::{LongShortForm, taxonomy};
use unic_langid::LanguageIdentifier;

#[cfg(feature = "csl-json")]
use citationberg::json as csl_json;

use super::citation_label::Alphanumerical;
use super::{DisambiguateState, InstanceContext, LocatorPayload};

pub trait EntryLike {
    fn resolve_number_variable(
        &self,
        variable: NumberVariable,
    ) -> Option<MaybeTyped<Cow<'_, Numeric>>>;
    fn resolve_page_variable(
        &self,
        variable: PageVariable,
    ) -> Option<MaybeTyped<PageRanges>>;
    fn resolve_standard_variable(
        &self,
        form: LongShortForm,
        variable: StandardVariable,
    ) -> Option<Cow<'_, ChunkedString>>;
    fn resolve_name_variable(&self, variable: NameVariable) -> Vec<Cow<'_, Person>>;
    fn resolve_date_variable(&self, variable: DateVariable) -> Option<Cow<'_, Date>>;
    /// A literal date value (`"in press"`, `"(in press)"`, …) for a date
    /// variable that has no machine-readable parts.
    fn resolve_date_literal(&self, variable: DateVariable) -> Option<Cow<'_, str>> {
        let _ = variable;
        None
    }
    fn matches_entry_type(&self, kind: taxonomy::Kind) -> bool;
    fn is_english(&self) -> Option<bool>;
    /// The item's IETF language tag, when it has one. Used for locale-aware
    /// case transforms (Turkish/Azeri dotted i).
    fn language(&self) -> Option<Cow<'_, str>> {
        None
    }
    fn key(&self) -> Cow<'_, str>;
}

impl<'a, T: EntryLike> InstanceContext<'a, T> {
    pub(super) fn resolve_number_variable(
        &self,
        variable: NumberVariable,
    ) -> Option<NumberVariableResult<'a>> {
        match variable {
            NumberVariable::CitationNumber => {
                Some(NumberVariableResult::Regular(MaybeTyped::Typed(Cow::Owned(
                    Numeric::from(self.cite_props.speculative.citation_number as u32 + 1),
                ))))
            }
            NumberVariable::FirstReferenceNoteNumber => {
                // Per CSL, the variable is empty on a first reference; it
                // carries the note number of the first citation on later
                // references (citeproc-js only populates it for subsequent
                // cites).
                if self.cite_props.certain.is_first_position() {
                    None
                } else {
                    self.cite_props.certain.first_note_number.map(|n| {
                        NumberVariableResult::Regular(MaybeTyped::Typed(Cow::Owned(
                            Numeric::from(n as u32),
                        )))
                    })
                }
            }
            NumberVariable::Locator => {
                match &self.cite_props.speculative.locator.as_ref()?.1 {
                    &LocatorPayload::Str(l) => Some(NumberVariableResult::from_regular(
                        Numeric::from_str(l)
                            .map(|n| MaybeTyped::Typed(Cow::Owned(n)))
                            .unwrap_or_else(|_| MaybeTyped::String(l.to_owned())),
                    )),
                    LocatorPayload::Transparent(_) => {
                        Some(NumberVariableResult::Transparent(
                            self.cite_props.certain.initial_idx,
                        ))
                    }
                }
            }
            _ => self
                .entry
                .resolve_number_variable(variable)
                .map(NumberVariableResult::from_regular),
        }
    }

    pub(super) fn resolve_page_variable(
        &self,
        variable: PageVariable,
    ) -> Option<PageVariableResult> {
        self.entry.resolve_page_variable(variable)
    }

    // Number variables are standard variables.
    pub(super) fn resolve_standard_variable(
        &self,
        form: LongShortForm,
        variable: StandardVariable,
    ) -> Option<Cow<'a, ChunkedString>> {
        match variable {
            StandardVariable::YearSuffix => self
                .cite_props
                .speculative
                .year_suffix
                .map(|s| Cow::Owned(StringChunk::normal(letter(s)).into())),
            _ => self.entry.resolve_standard_variable(form, variable),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum NumberVariableResult<'a> {
    Regular(MaybeTyped<Cow<'a, Numeric>>),
    Transparent(usize),
}

pub(super) type PageVariableResult = MaybeTyped<PageRanges>;

pub(super) enum NumberOrPageVariableResult<'a> {
    Number(NumberVariableResult<'a>),
    Page(PageVariableResult),
}

impl<'a> NumberVariableResult<'a> {
    pub(super) fn from_regular(regular: MaybeTyped<Cow<'a, Numeric>>) -> Self {
        Self::Regular(regular)
    }

    pub(super) fn csl_cmp(&self, other: &Self) -> cmp::Ordering {
        match (self, other) {
            (Self::Regular(a), Self::Regular(b)) => a.csl_cmp(b),
            (Self::Regular(_), Self::Transparent(_)) => cmp::Ordering::Less,
            (Self::Transparent(_), Self::Regular(_)) => cmp::Ordering::Greater,
            (Self::Transparent(a), Self::Transparent(b)) => a.cmp(b),
        }
    }
}

impl EntryLike for Entry {
    fn language(&self) -> Option<Cow<'_, str>> {
        self.language
            .as_ref()
            .map(|language| Cow::Owned(language.to_string()))
    }

    fn key(&self) -> Cow<'_, str> {
        Cow::Borrowed(self.key())
    }

    fn resolve_number_variable(
        &self,
        variable: NumberVariable,
    ) -> Option<MaybeTyped<Cow<'_, Numeric>>> {
        match variable {
            NumberVariable::ChapterNumber => self
                .chapter()
                .or_else(|| {
                    self.bound_select(
                        &select!(
                            (("e":Anthos) > ("p":Anthology)) |
                            (("e":*) > ("p":Reference)) |
                            (("e":Article) > ("p":Proceedings)) |
                            (("e":*) > ("p":Book))
                        ),
                        "e",
                    )
                    .and_then(Entry::volume)
                })
                .map(MaybeTyped::to_cow),
            NumberVariable::CitationNumber => panic!("processor must resolve this"),
            NumberVariable::CollectionNumber => {
                self.get_collection().and_then(Entry::volume).map(MaybeTyped::to_cow)
            }
            NumberVariable::Edition => self.map(|e| e.edition()).map(MaybeTyped::to_cow),
            NumberVariable::FirstReferenceNoteNumber => {
                panic!("processor must resolve this")
            }
            NumberVariable::Issue => self.map(|e| e.issue()).map(MaybeTyped::to_cow),
            NumberVariable::Locator => panic!("processor must resolve this"),
            NumberVariable::Number => self
                .serial_number()
                .and_then(|s| s.0.get("serial"))
                // Serial numbers should always be treated as untyped strings,
                // even if sometimes they are valid number ranges with affixes.
                .map(|s| MaybeTyped::String(s.to_owned()))
                .or_else(|| {
                    // User can specify either 'serial-number: 3' or
                    // 'chapter: 3' for chapter entries, with the same result.
                    self.bound_select(&select!(("e":Chapter)), "e")
                        .and_then(|s| s.chapter())
                        .map(MaybeTyped::to_cow)
                }),
            NumberVariable::NumberOfPages => {
                self.page_total().map(|n| MaybeTyped::Typed(Cow::Borrowed(n)))
            }
            NumberVariable::NumberOfVolumes => {
                self.volume_total().map(|n| MaybeTyped::Typed(Cow::Borrowed(n)))
            }
            NumberVariable::PageFirst => self
                .page_range()
                .and_then(MaybeTyped::as_typed)
                .and_then(PageRanges::first)
                .map(|r| MaybeTyped::Typed(Cow::Owned(r.clone()))),
            NumberVariable::PartNumber => self
                .bound_select(
                    &select!(
                        (("e":*) > (Article | Blog | Book | Legislation))
                    ),
                    "e",
                )
                .and_then(Entry::volume)
                .map(MaybeTyped::to_cow),
            NumberVariable::PrintingNumber => self
                .map(|e| e.serial_number())
                .and_then(|s| s.0.get("printing"))
                .map(|s| {
                    Numeric::from_str(s)
                        .map(|n| MaybeTyped::Typed(Cow::Owned(n)))
                        .unwrap_or_else(|_| MaybeTyped::String(s.to_owned()))
                }),
            NumberVariable::Section => None,
            NumberVariable::SupplementNumber => None,
            NumberVariable::Version => self
                .bound_select(&select!(("e":Repository)), "e")
                .and_then(Entry::serial_number)
                .and_then(|s| s.0.get("version"))
                .map(|s| {
                    Numeric::from_str(s)
                        .map(|n| MaybeTyped::Typed(Cow::Owned(n)))
                        .unwrap_or_else(|_| MaybeTyped::String(s.to_owned()))
                }),
            NumberVariable::Volume => self
                .get_container()
                .and_then(|e| e.volume())
                .or_else(|| self.volume())
                .map(MaybeTyped::to_cow),
        }
    }

    fn resolve_page_variable(
        &self,
        variable: PageVariable,
    ) -> Option<MaybeTyped<PageRanges>> {
        match variable {
            PageVariable::Page => self.page_range().cloned(),
        }
    }

    // Number variables are standard variables.
    fn resolve_standard_variable(
        &self,
        form: LongShortForm,
        variable: StandardVariable,
    ) -> Option<Cow<'_, ChunkedString>> {
        let entry = self;
        match variable {
            StandardVariable::Abstract => entry
                .map(|e| e.abstract_())
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::Annote => {
                entry.map(|e| e.note()).map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::Archive => {
                entry.map(|e| e.archive()).map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::ArchiveCollection => None,
            StandardVariable::ArchiveLocation => {
                entry.archive_location().map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::ArchivePlace => None,
            StandardVariable::Authority => {
                // `Entry::organization` may also appear as `StandardVariable::Publisher`.
                // See the comment in that arm.
                entry.organization().map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::CallNumber => {
                entry.call_number().map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::CitationKey => {
                Some(Cow::Owned(StringChunk::verbatim(&entry.key).into()))
            }
            StandardVariable::CitationLabel => {
                Some(Cow::Owned(Alphanumerical::default().citation(entry).into()))
            }
            // Get third-order title first, then second-order title.
            StandardVariable::CollectionTitle => entry
                .get_collection()
                .and_then(|e| e.title())
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::ContainerTitle => entry
                .get_container()
                .and_then(|e| e.title())
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::ContainerTitleShort => entry
                .get_container()
                .and_then(|e| e.title())
                .map(|f| f.select(LongShortForm::Short))
                .map(Cow::Borrowed),
            StandardVariable::Dimensions => entry
                .runtime()
                .map(|r| Cow::Owned(StringChunk::normal(r.to_string()).into())),
            StandardVariable::Division => None,
            StandardVariable::DOI => {
                entry.doi().map(|d| Cow::Owned(StringChunk::verbatim(d).into()))
            }
            StandardVariable::Event | StandardVariable::EventTitle => entry
                .bound_select(&select!(* > ("p":(Exhibition | Conference | Misc))), "p")
                .and_then(Entry::title)
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::EventPlace => entry
                .bound_select(&select!(* > ("p":(Exhibition | Conference | Misc))), "p")
                .and_then(Entry::location)
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::Genre => {
                entry.map(|e| e.genre()).map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::ISBN => {
                entry.isbn().map(|d| Cow::Owned(StringChunk::verbatim(d).into()))
            }
            StandardVariable::ISSN => {
                entry.issn().map(|d| Cow::Owned(StringChunk::verbatim(d).into()))
            }
            StandardVariable::Jurisdiction => None,
            StandardVariable::Keyword => None,
            StandardVariable::Language => entry
                .map(|e| e.language())
                .map(|l| Cow::Owned(StringChunk::normal(csl_language(l)).into())),
            StandardVariable::License => None,
            StandardVariable::Medium => None,
            StandardVariable::Note => {
                entry.note().map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::OriginalPublisher => entry
                .get_original()
                .and_then(|e| e.publisher())
                .and_then(Publisher::name)
                .map(|n| n.select(form))
                .map(Cow::Borrowed),
            StandardVariable::OriginalPublisherPlace => entry
                .get_original()
                .and_then(|e| e.publisher().and_then(|p| p.location()))
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::OriginalTitle => entry
                .get_original()
                .and_then(|e| e.title())
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::PartTitle => None,
            StandardVariable::PMCID => {
                entry.pmcid().map(|d| Cow::Owned(StringChunk::verbatim(d).into()))
            }
            StandardVariable::PMID => {
                entry.pmid().map(|d| Cow::Owned(StringChunk::verbatim(d).into()))
            }
            StandardVariable::Publisher => entry
                .map(|e| e.publisher())
                .and_then(Publisher::name)
                // Fallback to `organization` if `publisher` is missing.
                //
                // Many CSL styles use `<text variable="publisher"/>` to display
                // the university where a thesis was written, because Zotero
                // exports the university to `publisher` in CSL-JSON.
                //
                // However, Zotero exports university to `institution` in BibLaTeX.
                // In BibLaTeX, `publisher` and `institution` are separate fields
                // (`school` is an alias for `institution`). We map them to
                // `Entry::publisher` and `Entry::organization` respectively.
                //
                // Therefore, this fallback is necessary to make BibLaTeX data
                // usable for such CSL styles.
                .or_else(|| entry.organization())
                .map(|n| n.select(form))
                .map(Cow::Borrowed),
            StandardVariable::PublisherPlace => entry
                .map(|e| e.publisher())
                .and_then(|p| p.location())
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::References => None,
            StandardVariable::ReviewedGenre => None,
            StandardVariable::ReviewedTitle => None,
            StandardVariable::Scale => None,
            StandardVariable::Source => entry
                .bound_select(&select!(* > ("p":Repository)), "p")
                .and_then(Entry::title)
                .map(|f| f.select(form))
                .map(Cow::Borrowed),
            StandardVariable::Status => None,
            StandardVariable::Title => {
                entry.title().map(|f| f.select(form)).map(Cow::Borrowed)
            }
            StandardVariable::TitleShort => entry
                .title()
                .map(|f| f.select(LongShortForm::Short))
                .map(Cow::Borrowed),
            StandardVariable::URL => entry
                .map(|e| e.url())
                .map(|d| Cow::Owned(StringChunk::verbatim(d.to_string()).into())),
            StandardVariable::VolumeTitle => {
                let selector = select!(
                    (Anthos > ("p":Anthology)) |
                    (Entry  > ("p":*)) |
                    (* > ("p":Reference)) |
                    (Article > ("p":Proceedings))
                );

                self.bound_select(&selector, "p")
                    .and_then(Entry::title)
                    .map(|f| f.select(form))
                    .map(Cow::Borrowed)
            }
            StandardVariable::YearSuffix => panic!("processor must resolve this"),
        }
    }

    fn resolve_date_variable(&self, variable: DateVariable) -> Option<Cow<'_, Date>> {
        Some(Cow::Borrowed(match variable {
            DateVariable::Accessed => self.url_any().and_then(|u| u.visit_date.as_ref()),
            DateVariable::AvailableDate => None,
            DateVariable::EventDate => self
                .bound_select(&select!(* > ("p":(Exhibition | Conference | Misc))), "p")
                .and_then(Entry::date),
            DateVariable::Issued => self.date_any(),
            DateVariable::OriginalDate => self.get_original().and_then(|e| e.date()),
            DateVariable::Submitted => None,
        }?))
    }

    fn resolve_name_variable(
        &self,
        variable: taxonomy::NameVariable,
    ) -> Vec<Cow<'_, Person>> {
        match variable {
            NameVariable::Author => self.authors().map(|a| a.iter().collect()),
            NameVariable::Chair => self
                .bound_select(
                    &select!(
                        (* > ("p":(Proceedings | Conference)))
                    ),
                    "p",
                )
                .map(|e| e.affiliated_with_role(PersonRole::Director)),
            NameVariable::CollectionEditor => self
                .get_collection()
                .and_then(|e| e.editors())
                .map(|a| a.iter().collect()),
            NameVariable::Compiler => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Compiler)))
            }
            NameVariable::Composer => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Composer)))
            }
            NameVariable::ContainerAuthor => self
                .get_container()
                .and_then(|e| e.authors())
                .map(|a| a.iter().collect()),
            NameVariable::Contributor => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Collaborator)))
            }
            NameVariable::Curator => self
                .bound_select(
                    &select!(
                        (* > ("p":Exhibition))
                    ),
                    "p",
                )
                .map(|e| e.affiliated_with_role(PersonRole::Organizer)),
            NameVariable::Director => self
                .bound_select(
                    &select!(
                        (* > ("p":(Audio | Video))) | ("p":(Audio | Video))
                    ),
                    "p",
                )
                .map(|e| e.affiliated_with_role(PersonRole::Director)),
            NameVariable::Editor => {
                self.editors().map(|a| a.iter().collect()).or_else(|| {
                    self.get_container()
                        .and_then(|e| e.editors())
                        .map(|a| a.iter().collect())
                })
            }
            NameVariable::EditorialDirector => None,
            NameVariable::EditorTranslator => {
                let translator = self.affiliated_with_role(PersonRole::Translator);
                Some(
                    self.editors()
                        .unwrap_or_default()
                        .iter()
                        .filter(|e| translator.contains(e))
                        .collect(),
                )
            }
            NameVariable::ExecutiveProducer => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::ExecutiveProducer)))
            }
            NameVariable::Guest => None,
            NameVariable::Host => None,
            NameVariable::Illustrator => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Illustrator)))
            }
            NameVariable::Interviewer => None,
            NameVariable::Narrator => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Narrator)))
            }
            NameVariable::Organizer => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Organizer)))
            }
            NameVariable::OriginalAuthor => self
                .get_original()
                .and_then(|e| e.authors())
                .map(|a| a.iter().collect()),
            NameVariable::Performer => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::CastMember)))
            }
            NameVariable::Producer => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Producer)))
            }
            NameVariable::Recipient => None,
            NameVariable::ReviewedAuthor => None,
            NameVariable::ScriptWriter => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Writer)))
            }
            NameVariable::SeriesCreator => self
                .bound_select(
                    &select!(
                        (* > ("p":(Audio | Video))) | ("p":(Audio | Video))
                    ),
                    "p",
                )
                .map(|e| e.affiliated_with_role(PersonRole::Founder)),
            NameVariable::Translator => {
                self.map(|e| Some(e.affiliated_with_role(PersonRole::Translator)))
            }
        }
        .unwrap_or_default()
        .into_iter()
        .map(Cow::Borrowed)
        .collect()
    }

    fn matches_entry_type(&self, kind: citationberg::taxonomy::Kind) -> bool {
        // Each match arm contains mutually exclusive entry kinds.
        match kind {
            Kind::Article
            | Kind::ArticleMagazine
            | Kind::ArticleNewspaper
            | Kind::ArticleJournal
            | Kind::PaperConference
            | Kind::Report
            | Kind::Thesis
            | Kind::Manuscript => {
                if kind == Kind::ArticleMagazine {
                    // TODO: Hayagriva does not differentiate between scientific and
                    // non-scientific magazines. Could disambiguate via presence of
                    // DOI or similar.
                    return false;
                }

                let is_journal = select!(Article > Periodical).matches(self);
                if kind == Kind::ArticleJournal {
                    return is_journal;
                }

                let is_news = select!(Article > Newspaper).matches(self);
                if kind == Kind::ArticleNewspaper {
                    return is_news;
                }

                let is_conference = select!(Article > Proceedings).matches(self);
                if kind == Kind::PaperConference {
                    return is_conference;
                }

                let is_report = select!((* > Report) | Report).matches(self);
                if kind == Kind::Report {
                    return is_report;
                }

                let is_thesis = select!((* > Thesis) | Thesis).matches(self);
                if kind == Kind::Thesis {
                    return is_thesis;
                }

                let is_manuscript = self.entry_type() == &EntryType::Manuscript;
                if kind == Kind::Manuscript {
                    return is_manuscript;
                }

                self.entry_type() == &EntryType::Article
                    && !select!(* > Blog).matches(self)
                    && !(is_journal
                        || is_news
                        || is_conference
                        || is_report
                        || is_thesis
                        || is_manuscript)
            }
            Kind::Book | Kind::Classic | Kind::Periodical | Kind::Collection => {
                if !select!(Book | Anthology | Proceedings).matches(self) {
                    return false;
                }

                if kind == Kind::Classic {
                    // TODO: Hayagriva does not support indicating something is a
                    // classic.
                    return false;
                }

                let is_periodical =
                    select!((Book > Periodical) | Periodical).matches(self);
                if kind == Kind::Periodical {
                    return is_periodical;
                }

                let is_collection = self.entry_type() == &EntryType::Anthology;
                if kind == Kind::Collection {
                    return is_collection;
                }

                !(is_periodical || is_collection)
            }
            Kind::Chapter => select!(
                (Anthos > Anthology) | (Chapter > (Book | Anthology | Proceedings))
            )
            .matches(self),
            Kind::Entry | Kind::EntryDictionary | Kind::EntryEncyclopedia => {
                if kind == Kind::EntryDictionary {
                    // TODO: We do not differentiate between dictionaries and other
                    // references.
                    return false;
                }

                let is_encyclopedia = select!(* > Reference).matches(self);
                if kind == Kind::EntryEncyclopedia {
                    return is_encyclopedia;
                }

                self.entry_type() == &EntryType::Entry && !is_encyclopedia
            }
            Kind::Event => self.entry_type() == &EntryType::Exhibition,
            Kind::Hearing | Kind::Interview | Kind::Performance | Kind::Speech => false,
            Kind::Broadcast | Kind::MotionPicture | Kind::MusicalScore | Kind::Song => {
                let is_music_score =
                    select!(Audio > (Book | Periodical | Reference | Misc | Blog | Web))
                        .matches(self);
                if kind == Kind::MusicalScore {
                    return is_music_score;
                }

                let is_motion_picture =
                    self.entry_type() == &EntryType::Video && self.parents().is_empty();
                if kind == Kind::MotionPicture {
                    return is_motion_picture;
                }

                let is_song =
                    self.entry_type() == &EntryType::Audio && self.parents().is_empty();
                if kind == Kind::Song {
                    return is_song;
                }

                matches!(self.entry_type(), EntryType::Audio | EntryType::Video)
                    && !(is_music_score || is_motion_picture || is_song)
            }
            Kind::Legislation | Kind::Bill => {
                if self.entry_type() != &EntryType::Legislation {
                    return false;
                }

                let is_published = self.publisher().is_some();
                if kind == Kind::Bill {
                    return !is_published;
                }

                is_published
            }
            Kind::LegalCase => self.entry_type() == &EntryType::Case,
            Kind::Regulation | Kind::Standard | Kind::Treaty => false,
            Kind::Patent => self.entry_type() == &EntryType::Patent,
            Kind::Webpage | Kind::PostWeblog | Kind::Post => {
                let is_blogpost = select!(* > Blog).matches(self);
                if kind == Kind::PostWeblog {
                    return is_blogpost;
                }

                let is_post = select!(Post | (* > Thread)).matches(self);
                if kind == Kind::Post {
                    return is_post;
                }

                select!((Misc["url"]) | (* > (Web | Blog)) | Web | Blog | Thread)
                    .matches(self)
                    && !(is_blogpost || is_post)
            }
            Kind::Dataset => false,
            Kind::Figure | Kind::Graphic | Kind::Map => {
                let is_figure = select!(Artwork > Article).matches(self);
                if kind == Kind::Figure {
                    return is_figure;
                }

                if kind == Kind::Map {
                    return false;
                }

                self.entry_type() == &EntryType::Artwork && !is_figure
            }
            Kind::Pamphlet => false,
            Kind::PersonalCommunication => false,
            Kind::Review | Kind::ReviewBook => false,
            Kind::Software => self.entry_type() == &EntryType::Repository,
            Kind::Document => self.entry_type() == &EntryType::Misc,
        }
    }

    fn is_english(&self) -> Option<bool> {
        self.language().map(|l| l.language.as_str() == "en")
    }
}

#[cfg(feature = "csl-json")]
fn resolve_csl_json_standard_variable(
    item: &citationberg::json::Item,
    variable: StandardVariable,
) -> Option<Cow<'_, ChunkedString>> {
    match item.0.get(&variable.to_string())? {
        csl_json::Value::String(s) => {
            Some(Cow::Owned(StringChunk::normal(s.clone()).into()))
        }
        csl_json::Value::Number(n) => {
            Some(Cow::Owned(StringChunk::normal(n.to_string()).into()))
        }
        _ => None,
    }
}

/// Resolve a CSL-JSON field with its Zotero short-form aliases.
///
/// citeproc-js maps `shortTitle` to `title-short` and `journalAbbreviation` to
/// `container-title-short` when the canonical field is absent, and a
/// `form="short"` request for `title`/`container-title` falls back to the
/// `-short` field, then to the long field
/// (`CSL.Engine.prototype.getTextSubField`, `VARIABLES_WITH_SHORT_FORM`).
#[cfg(feature = "csl-json")]
fn resolve_csl_json_short_or_long<'a>(
    item: &'a citationberg::json::Item,
    short: &str,
    long: &str,
    alias: &str,
) -> Option<Cow<'a, ChunkedString>> {
    resolve_csl_json_field(item, short)
        .or_else(|| resolve_csl_json_field(item, alias))
        .or_else(|| resolve_csl_json_field(item, long))
}

#[cfg(feature = "csl-json")]
fn resolve_csl_json_field<'a>(
    item: &'a citationberg::json::Item,
    key: &str,
) -> Option<Cow<'a, ChunkedString>> {
    match item.0.get(key)? {
        csl_json::Value::String(s) => {
            Some(Cow::Owned(StringChunk::normal(s.clone()).into()))
        }
        csl_json::Value::Number(n) => {
            Some(Cow::Owned(StringChunk::normal(n.to_string()).into()))
        }
        _ => None,
    }
}

/// CSL-JSON name variables in the order citeproc-js tries them when it needs a
/// representative creator (`CSL.NAME_VARIABLES`).
#[cfg(feature = "csl-json")]
const CSL_JSON_NAME_VARIABLE_ORDER: &[&str] = &[
    "author",
    "chair",
    "collection-editor",
    "compiler",
    "composer",
    "container-author",
    "contributor",
    "curator",
    "director",
    "editor",
    "editor-translator",
    "editorial-director",
    "executive-producer",
    "guest",
    "host",
    "illustrator",
    "interviewer",
    "narrator",
    "organizer",
    "original-author",
    "performer",
    "producer",
    "recipient",
    "reviewed-author",
    "script-writer",
    "series-creator",
    "translator",
    "commenter",
];

/// Whether a character survives citeproc-js's `ROMANESQUE_NOT_REGEXP` filter
/// used when building citation labels.
#[cfg(feature = "csl-json")]
fn is_romanesque_label_char(c: char) -> bool {
    c.is_ascii_alphabetic()
        || matches!(
            c,
            '\u{00c0}'..='\u{017f}' // Latin-1 Supplement/Latin Extended-A
                | '\u{0218}'..='\u{021b}'
                | '\u{0370}'..='\u{03ff}' // Greek
                | '\u{0400}'..='\u{052f}' // Cyrillic
                | '\u{0590}'..='\u{05d4}' // Hebrew
                | '\u{05d6}'..='\u{05ff}'
                | '\u{0600}'..='\u{06ff}' // Arabic
                | '\u{0e01}'..='\u{0e5b}' // Thai
                | '\u{1f00}'..='\u{1fff}' // Greek Extended
                | '\u{200c}'..='\u{200e}' // ZWNJ, ZWJ, LRM
                | '\u{202a}'..='\u{202e}' // Bidi controls
        )
}

/// Build the alphanumeric citation label that citeproc-js generates from the
/// first present name variable and the issued year (`getCitationLabel`).
///
/// The default trigraph is `Aaaa00:AaAa00:AaAA00:AAAA00`: one author keeps up
/// to four family-name letters, two authors two each, three authors 2+1+1, and
/// four or more one letter each. The last two digits of the year follow.
#[cfg(feature = "csl-json")]
fn csl_json_citation_label(item: &citationberg::json::Item) -> String {
    // A label supplied by the data wins over the computed one.
    if let Some(csl_json::Value::String(label)) = item.0.get("citation-label") {
        return label.clone();
    }

    let mut label = String::new();
    'outer: for key in CSL_JSON_NAME_VARIABLE_ORDER {
        let Some(csl_json::Value::Names(names)) = item.0.get(*key) else {
            continue;
        };
        if names.is_empty() {
            continue;
        }
        let widths: &[usize] = match names.len() {
            1 => &[4],
            2 => &[2, 2],
            3 => &[2, 1, 1],
            _ => &[1, 1, 1, 1],
        };
        for (name, width) in names.iter().zip(widths) {
            let family = match name {
                csl_json::NameValue::Item(item) => item.family.as_str(),
                csl_json::NameValue::Literal(literal) => literal.literal.as_str(),
            };
            let mut family = family;
            // Strip a leading lowercase particle ("van ", "de la ").
            if let Some(space) = family.find(' ') {
                let prefix = &family[..space];
                if !prefix.is_empty()
                    && prefix
                        .chars()
                        .all(|c| c.is_ascii_lowercase() || c == '\'' || c == '\u{2019}')
                {
                    family = family[space..].trim_start();
                }
            }
            // Strip a leading article.
            let lower = family.to_lowercase();
            for article in ["a ", "an ", "the "] {
                if lower.starts_with(article) && family.is_char_boundary(article.len()) {
                    family = &family[article.len()..];
                    break;
                }
            }
            let cleaned: String =
                family.chars().filter(|c| is_romanesque_label_char(*c)).collect();
            if cleaned.is_empty() {
                break 'outer;
            }
            let mut part: String = cleaned.chars().take(*width).collect();
            if part.chars().count() > 1 {
                let mut chars = part.chars();
                let first = chars.next().unwrap().to_uppercase().to_string();
                part = first + &chars.as_str().to_lowercase();
            } else {
                part = part.to_uppercase();
            }
            label.push_str(&part);
        }
        break;
    }

    if label.is_empty()
        && let Some(csl_json::Value::String(title)) = item.0.get("title")
    {
        let joined: String = title.split_whitespace().collect();
        let mut part: String = joined.chars().take(4).collect();
        if part.chars().count() > 1 {
            let mut chars = part.chars();
            let first = chars.next().unwrap().to_uppercase().to_string();
            part = first + &chars.as_str().to_lowercase();
        } else {
            part = part.to_uppercase();
        }
        label = part;
    }

    let year = match item.0.get("issued") {
        Some(csl_json::Value::Date(csl_json::DateValue::DateParts {
            date_parts,
            ..
        })) => date_parts.0.first().and_then(|d| d.0.first()).copied().unwrap_or(0),
        Some(csl_json::Value::Date(csl_json::DateValue::Raw { raw, .. })) => {
            raw.start.year
        }
        _ => 0,
    };
    let year = year.to_string();
    let digits = if year.len() >= 2 { &year[year.len() - 2..] } else { "00" };
    label.push_str(digits);

    label
}

#[cfg(feature = "csl-json")]
/// Split a citation-processing suffix out of a CSL-JSON `given` field.
///
/// citeproc-js's name parsing (`CSL.parseParticles`' `parseSuffix`) treats a
/// comma in the given name as the start of a suffix: `"John, III"` is given
/// `"John"` plus suffix `"III"`, and `"John,! Jr."` additionally marks that a
/// comma should separate the suffix when it is appended.
/// citeproc-js's `_parseName`: a family name wrapped in double quotes is
/// literal and must not be particle-parsed; the quotes are removed.
fn unquote_family(family: &str) -> String {
    if family.len() >= 2 && family.starts_with('"') && family.ends_with('"') {
        family[1..family.len() - 1].to_string()
    } else {
        family.to_string()
    }
}

/// Move a trailing lower-case particle in the given name (`François Hédelin
/// d'`) into the dropping-particle slot, matching citeproc-js's name parser.
fn split_given_particle(given: Option<String>) -> (Option<String>, Option<String>) {
    let Some(given) = given else { return (None, None) };
    let Some(idx) = given.rfind(' ') else { return (Some(given), None) };
    let particle = &given[idx + 1..];
    let base = &given[..idx];
    if particle.starts_with(|c: char| c.is_lowercase())
        && (particle.ends_with('\'') || particle.ends_with('\u{2019}'))
        && crate::lang::name::NAME_PARTICLES
            .binary_search(&particle.to_lowercase().as_str())
            .is_ok()
    {
        (Some(base.to_string()), Some(particle.to_string()))
    } else {
        (Some(given), None)
    }
}

fn split_given_suffix(
    given: Option<&str>,
    suffix: Option<&str>,
    comma_suffix: bool,
) -> (Option<String>, Option<String>, bool) {
    if suffix.is_some() {
        return (given.map(str::to_string), suffix.map(str::to_string), comma_suffix);
    }
    let Some(given) = given else {
        return (None, None, comma_suffix);
    };

    // Mirrors `/(\s*,!*\s*)/`: whitespace, a comma, optional `!`, whitespace.
    let bytes = given.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b',' {
            let mut start = i;
            while start > 0 && bytes[start - 1].is_ascii_whitespace() {
                start -= 1;
            }
            let mut end = i + 1;
            while bytes.get(end) == Some(&b'!') {
                end += 1;
            }
            while bytes.get(end).is_some_and(u8::is_ascii_whitespace) {
                end += 1;
            }

            let separator = &given[start..end];
            let comma = separator.chars().filter(|c| !c.is_whitespace()).count() == 2;
            let rest = &given[end..];
            if !rest.is_empty() {
                return (
                    Some(given[..start].to_string()),
                    Some(rest.to_string()),
                    comma_suffix || comma,
                );
            }
            break;
        }
        i += 1;
    }

    (Some(given.to_string()), None, comma_suffix)
}

impl EntryLike for citationberg::json::Item {
    fn resolve_standard_variable(
        &self,
        form: LongShortForm,
        variable: StandardVariable,
    ) -> Option<Cow<'_, ChunkedString>> {
        match variable {
            // Per citeproc tests, a 'title-short' without 'title' is valid
            // and should be used when the short form is selected; the long
            // title is the fallback.
            StandardVariable::Title => match form {
                LongShortForm::Short => resolve_csl_json_short_or_long(
                    self,
                    "title-short",
                    "title",
                    "shortTitle",
                ),
                LongShortForm::Long => resolve_csl_json_field(self, "title"),
            },
            // An explicit `*-short` variable is strict: citeproc-js returns
            // nothing when the short field is absent (only the `form="short"`
            // request on the long variable falls back).
            StandardVariable::TitleShort => resolve_csl_json_field(self, "title-short")
                .or_else(|| resolve_csl_json_field(self, "shortTitle")),
            StandardVariable::ContainerTitle => match form {
                LongShortForm::Short => resolve_csl_json_short_or_long(
                    self,
                    "container-title-short",
                    "container-title",
                    "journalAbbreviation",
                ),
                LongShortForm::Long => resolve_csl_json_field(self, "container-title"),
            },
            StandardVariable::ContainerTitleShort => {
                resolve_csl_json_field(self, "container-title-short")
                    .or_else(|| resolve_csl_json_field(self, "journalAbbreviation"))
            }
            StandardVariable::CitationLabel => {
                let label = csl_json_citation_label(self);
                (!label.is_empty()).then(|| Cow::Owned(StringChunk::normal(label).into()))
            }
            _ => resolve_csl_json_standard_variable(self, variable),
        }
    }

    fn resolve_date_variable(&self, variable: DateVariable) -> Option<Cow<'_, Date>> {
        match self.0.get(&variable.to_string())? {
            csl_json::Value::Date(d) => {
                let Ok(d) = csl_json::FixedDateRange::try_from(d.clone()) else {
                    return None;
                };
                if d.end.is_some() {
                    panic!("ranges are not supported")
                }
                let d = d.start;

                // CSL-JSON numbers years historically (year -250 is 250 BCE)
                // while the internal representation uses 0 for 1 BCE
                // (cf. `Date` and `write_year`).
                let year = if d.year <= 0 { d.year as i32 + 1 } else { d.year as i32 };

                // citeproc-js normalizes out-of-range month values at render
                // time (`CSL.Util.Dates.normalizeMonth`): values outside
                // 1-24 are invalid, 17-24 wrap back into the 13-16 season
                // range, and 13-16 name a season rather than a month.
                let mut month = None;
                let mut season = d.season;
                if let Some(raw) = d.month {
                    let mut num = raw as i32 + 1;
                    if (1..=24).contains(&num) {
                        while num > 16 {
                            num -= 4;
                        }
                        if num > 12 {
                            season = citationberg::taxonomy::Season::try_from_csl_number(
                                (num - 12) as u8,
                            )
                            .ok();
                        } else {
                            month = Some((num - 1) as u8);
                        }
                    }
                }

                Some(Cow::Owned(Date {
                    year,
                    month,
                    day: d.day,
                    approximate: d.circa,
                    season,
                }))
            }
            _ => None,
        }
    }

    fn resolve_date_literal(&self, variable: DateVariable) -> Option<Cow<'_, str>> {
        match self.0.get(&variable.to_string())? {
            csl_json::Value::Date(csl_json::DateValue::Raw {
                literal: Some(l), ..
            })
            | csl_json::Value::Date(csl_json::DateValue::DateParts {
                literal: Some(l),
                ..
            }) => Some(Cow::Borrowed(l.as_str())),
            _ => None,
        }
    }

    fn resolve_name_variable(&self, variable: NameVariable) -> Vec<Cow<'_, Person>> {
        match self.0.get(&variable.to_string()) {
            Some(csl_json::Value::Names(names)) => names
                .iter()
                .map(|name| {
                    Cow::Owned(match name {
                        csl_json::NameValue::Literal(l) => Person {
                            name: l.literal.clone(),
                            prefix: None,
                            suffix: None,
                            given_name: None,
                            alias: None,
                            comma_suffix: false,
                            literal_family: true,
                            non_dropping_particle: None,
                        },
                        // CSL-JSON `family` is the family name verbatim: no
                        // particle heuristics. Particles only arrive through
                        // the explicit `non-dropping-particle` /
                        // `dropping-particle` fields (next arm). Calling
                        // `Person::from_strings` here split names like
                        // "van der Berg" into a dropping particle, which then
                        // disappeared in short form and reordered in long form
                        // (cf. upstream issue #382, "Della Porta").
                        csl_json::NameValue::Item(csl_json::NameItem {
                            family,
                            given,
                            non_dropping_particle: None,
                            dropping_particle: None,
                            suffix,
                            comma_suffix,
                        }) => {
                            let (given, suffix, comma_suffix) = split_given_suffix(
                                given.as_deref(),
                                suffix.as_deref(),
                                comma_suffix.unwrap_or_default(),
                            );
                            let given = given.filter(|given| !given.is_empty());
                            let (given, given_particle) = split_given_particle(given);
                            let literal_family =
                                family.starts_with('"') && family.ends_with('"');
                            Person {
                                name: unquote_family(family),
                                prefix: given_particle,
                                suffix,
                                given_name: given,
                                alias: None,
                                comma_suffix,
                                literal_family,
                                non_dropping_particle: None,
                            }
                        }
                        csl_json::NameValue::Item(csl_json::NameItem {
                            family,
                            given,
                            non_dropping_particle,
                            dropping_particle,
                            suffix,
                            comma_suffix,
                        }) => {
                            let (given, suffix, comma_suffix) = split_given_suffix(
                                given.as_deref(),
                                suffix.as_deref(),
                                comma_suffix.unwrap_or_default(),
                            );
                            let given = given.filter(|given| !given.is_empty());
                            let (given, given_particle) = split_given_particle(given);
                            Person {
                                name: unquote_family(family),
                                prefix: dropping_particle.clone().or(given_particle),
                                suffix,
                                given_name: given,
                                alias: None,
                                comma_suffix,
                                literal_family: false,
                                non_dropping_particle: non_dropping_particle.clone(),
                            }
                        }
                    })
                })
                .collect(),
            _ => vec![],
        }
    }

    fn resolve_page_variable(
        &self,
        variable: PageVariable,
    ) -> Option<MaybeTyped<PageRanges>> {
        match variable {
            PageVariable::Page => match self.0.get("page")? {
                &csl_json::Value::Number(n) => {
                    // Page ranges use i32 internally, so we check whether the
                    // number is in range.
                    Some(match i32::try_from(n) {
                        Ok(n) => MaybeTyped::Typed(PageRanges::from(n)),
                        // If the number is not in range, we degrade to a
                        // string, which disables some CSL features.
                        Err(_) => MaybeTyped::String(n.to_string()),
                    })
                }
                csl_json::Value::String(s) => {
                    let res = MaybeTyped::<PageRanges>::infallible_from_str(s);
                    Some(match res {
                        MaybeTyped::String(s) => MaybeTyped::String(s),
                        MaybeTyped::Typed(r) => MaybeTyped::Typed(r),
                    })
                }
                _ => None,
            },
        }
    }

    fn resolve_number_variable(
        &self,
        variable: NumberVariable,
    ) -> Option<MaybeTyped<Cow<'_, Numeric>>> {
        if matches!(variable, NumberVariable::PageFirst)
            && let Some(MaybeTyped::Typed(n)) =
                self.resolve_page_variable(PageVariable::Page)
        {
            return n.first().map(|r| MaybeTyped::Typed(Cow::Owned(r.clone())));
        }
        match self.0.get(&variable.to_string())? {
            csl_json::Value::Number(n) => {
                Some(MaybeTyped::Typed(Cow::Owned(Numeric::from(*n as u32))))
            }
            csl_json::Value::String(s) => {
                let res = MaybeTyped::<Numeric>::infallible_from_str(s);
                Some(match res {
                    MaybeTyped::String(s) => MaybeTyped::String(s),
                    MaybeTyped::Typed(n) => MaybeTyped::Typed(Cow::Owned(n)),
                })
            }
            _ => None,
        }
    }

    fn matches_entry_type(&self, kind: taxonomy::Kind) -> bool {
        let Some(actual) = self.0.get("type") else {
            return false;
        };
        let Some(string) = actual.to_str() else {
            return false;
        };
        Kind::from_str(&string) == Ok(kind)
    }

    fn is_english(&self) -> Option<bool> {
        self.0
            .get("language")
            .and_then(|l| l.to_str())
            .map(|l| l.starts_with("en"))
    }

    fn language(&self) -> Option<Cow<'_, str>> {
        self.0
            .get("language")
            .and_then(|l| l.to_str())
            .map(|l| Cow::Owned(l.to_string()))
    }

    fn key(&self) -> Cow<'_, str> {
        self.id().unwrap_or_default()
    }
}

pub(super) fn csl_language(lang_id: &LanguageIdentifier) -> String {
    let mut buf = String::with_capacity(if lang_id.region.is_some() { 5 } else { 2 });
    buf.push_str(lang_id.language.as_str());
    if let Some(region) = lang_id.region {
        buf.push('-');
        buf.push_str(region.as_str());
    }
    buf
}

// A function that takes a usize value and returns a String
fn letter(val: u8) -> String {
    let mut result = String::with_capacity(1);
    let mut current = val;

    loop {
        let remainder = current % 26;
        let c = (remainder + b'a') as char;
        result.insert(0, c);

        if current < 26 {
            break;
        }

        current = (current - 26) / 26;
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{from_biblatex_str, from_yaml_str};

    #[test]
    fn zotero_university_interop() {
        let entry = from_biblatex_str(
        r#"
        @thesis{zotero-export-better-biblatex,
            type = {Unpublished master’s thesis},
            title = {Fathers’ Participation in Family Work: {{Consequences}} for Fathers’ Stress and Father-Child Relations},
            author = {Almeida, David M.},
            namea = {Galambos, Nancy L.},
            nameatype = {collaborator},
            date = {1990-11},
            institution = {University of Victoria},
            location = {Victoria, British Columbia, Canada},
            langid = {american}
        }
        "#,
    ).unwrap().into_iter().next().unwrap();
        assert_eq!(entry.publisher().unwrap().name(), None);
        assert_eq!(
            entry.publisher().unwrap().location().unwrap(),
            &"Victoria, British Columbia, Canada".parse().unwrap()
        );
        assert_eq!(
            entry.organization().unwrap(),
            &"University of Victoria".parse().unwrap()
        );

        assert_eq!(
            entry
                .resolve_standard_variable(
                    Default::default(),
                    StandardVariable::Publisher
                )
                .unwrap()
                .to_str(),
            "University of Victoria"
        );
        assert_eq!(
            entry
                .resolve_standard_variable(
                    Default::default(),
                    StandardVariable::PublisherPlace
                )
                .unwrap()
                .to_str(),
            "Victoria, British Columbia, Canada"
        );
    }

    #[test]
    fn verbatim_serial_number() {
        let entry = from_yaml_str(
            // https://github.com/typst/hayagriva/issues/506
            r#"
            report:
              type: report
              serial-number: USDL-26-0599
              volume: XY-1-5
            "#,
        )
        .unwrap()
        .into_iter()
        .next()
        .unwrap();
        // Hyphens in serial numbers should not be converted to en dashes.
        assert_eq!(
            entry
                .resolve_number_variable(NumberVariable::Number)
                .unwrap()
                .to_str(),
            "USDL-26-0599"
        );
        // A hyphen after a non-numeric prefix is part of the identifier, not
        // a range delimiter: citeproc-js keeps `XY-1-5` verbatim (F-111).
        assert_eq!(
            entry
                .resolve_number_variable(NumberVariable::Volume)
                .unwrap()
                .to_str(),
            "XY-1-5"
        );
    }
}
