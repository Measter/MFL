// Basically a minor modification to codespan_reportings SimpleFiles because I wanted
// a more strongly-typed file ID.

use std::ops::Range;

use ariadne::{Cache, Source, Span};
use intcast::IntCast;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(u16);

impl FileId {
    #[inline(always)]
    pub const fn blank() -> Self {
        Self(0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation {
    pub file_id: FileId,
    pub source_start: u32,
    pub source_end: u32,
}

impl Default for SourceLocation {
    fn default() -> Self {
        Self {
            file_id: FileId::blank(),
            source_start: Default::default(),
            source_end: Default::default(),
        }
    }
}

impl Span for SourceLocation {
    type SourceId = FileId;

    fn source(&self) -> &Self::SourceId {
        &self.file_id
    }

    fn start(&self) -> usize {
        self.source_start.to_usize()
    }

    fn end(&self) -> usize {
        self.source_end.to_usize()
    }
}

impl SourceLocation {
    pub fn new(file_id: FileId, range: Range<u32>) -> Self {
        Self {
            file_id,
            source_start: range.start,
            source_end: range.end,
        }
    }

    #[inline(always)]
    #[allow(unused)]
    pub fn merge(self, other: Self) -> Self {
        assert!(self.file_id == other.file_id);
        Self {
            file_id: self.file_id,
            source_start: self.source_start.min(other.source_start),
            source_end: self.source_end.max(other.source_end),
        }
    }
}

struct LoadedSource {
    name: String,
    contents: String,
    source: Source,
}

#[derive(Default)]
pub struct SourceStorage {
    files: Vec<LoadedSource>,
}

impl SourceStorage {
    pub const fn new() -> Self {
        SourceStorage { files: Vec::new() }
    }

    pub fn add(&mut self, name: &str, source: &str) -> FileId {
        let id = self.files.len();
        self.files.push(LoadedSource {
            name: name.to_owned(),
            contents: source.to_owned(),
            source: source.into(),
        });

        FileId(id.to_u16().unwrap())
    }

    pub fn name(&self, id: FileId) -> &str {
        &self.files[id.0.to_usize()].name
    }

    pub fn source(&self, id: FileId) -> &str {
        &self.files[id.0.to_usize()].contents
    }
}

impl Cache<FileId> for &SourceStorage {
    fn fetch(&mut self, id: &FileId) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        Ok(&self.files[id.0.to_usize()].source)
    }

    fn display<'a>(&self, id: &'a FileId) -> Option<Box<dyn std::fmt::Display + 'a>> {
        let name = &self.files[id.0.to_usize()].name;

        Some(Box::new(name.clone()))
    }
}
