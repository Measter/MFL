// Basically a minor modification to codespan_reportings SimpleFiles because I wanted
// a more strongly-typed file ID.

use std::ops::Range;

use ariadne::{Cache, Source, Span};
use intcast::IntCast;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(u16);
impl FileId {
    pub fn dud() -> Self {
        Self(u16::MAX)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation {
    pub file_id: FileId,
    pub source_start: u32,
    pub len: u16,
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
        self.source_start.to_usize() + self.len.to_usize()
    }
}

impl SourceLocation {
    pub fn new(file_id: FileId, range: Range<u32>) -> Self {
        Self {
            file_id,
            source_start: range.start,
            len: (range.end - range.start).to_u16().unwrap(),
        }
    }

    #[inline(always)]
    #[allow(unused)]
    pub fn merge(self, other: Self) -> Self {
        assert!(self.file_id == other.file_id);
        let start = self.start().min(other.start());
        let end = self.end().max(other.end());
        let len = end - start;
        Self {
            file_id: self.file_id,
            source_start: start.to_u32().unwrap(),
            len: len.to_u16().unwrap(),
        }
    }

    pub fn neighbour_of(self, other: Self) -> bool {
        self.source_start + self.len.to_u32() == other.source_start
            || other.source_start + other.len.to_u32() == self.source_start
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
