// Basically a minor modification to codespan_reportings SimpleFiles because I wanted
// a more strongly-typed file ID.

use std::ops::Range;

use ariadne::{Cache, Source, Span};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl FileId {
    #[inline(always)]
    pub const fn blank() -> Self {
        Self(0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation {
    pub file_id: FileId,
    pub source_start: usize,
    pub source_end: usize,
    pub line: usize,
    pub column: usize,
}

impl Default for SourceLocation {
    fn default() -> Self {
        Self {
            file_id: FileId::blank(),
            source_start: Default::default(),
            source_end: Default::default(),
            line: Default::default(),
            column: Default::default(),
        }
    }
}

impl Span for SourceLocation {
    type SourceId = FileId;

    fn source(&self) -> &Self::SourceId {
        &self.file_id
    }

    fn start(&self) -> usize {
        self.source_start
    }

    fn end(&self) -> usize {
        self.source_end
    }
}

impl SourceLocation {
    pub fn new(file_id: FileId, range: Range<usize>, line: usize, column: usize) -> Self {
        Self {
            file_id,
            source_start: range.start,
            source_end: range.end,
            line,
            column,
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
            line: self.line.min(other.line),
            column: self.column.min(other.column),
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

        FileId(id)
    }

    pub fn name(&self, id: FileId) -> &str {
        &self.files[id.0].name
    }

    pub fn source(&self, id: FileId) -> &str {
        &self.files[id.0].contents
    }
}

impl Cache<FileId> for &SourceStorage {
    fn fetch(&mut self, id: &FileId) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        Ok(&self.files[id.0].source)
    }

    fn display<'a>(&self, id: &'a FileId) -> Option<Box<dyn std::fmt::Display + 'a>> {
        let name = &self.files[id.0].name;

        Some(Box::new(name.clone()))
    }
}
