// Basically a minor modification to codespan_reportings SimpleFiles because I wanted
// a more strongly-typed file ID.

use std::{ops::Range, path::Path};

use ariadne::{Cache, Source, Span};
use intcast::IntCast;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(u16);
impl FileId {
    pub fn dud() -> Self {
        Self(u16::MAX)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceLocation {
    pub file_id: FileId,
    pub source_start: u32,
    pub len: u16,
}

impl Span for SourceLocation {
    type SourceId = FileId;

    #[inline]
    fn source(&self) -> &Self::SourceId {
        &self.file_id
    }

    #[inline]
    fn start(&self) -> usize {
        self.source_start.to_usize()
    }

    #[inline]
    fn end(&self) -> usize {
        self.source_start.to_usize() + self.len.to_usize()
    }
}

impl SourceLocation {
    #[inline]
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

    #[inline]
    pub fn neighbour_of(self, other: Self) -> bool {
        self.source_start + self.len.to_u32() == other.source_start
            || other.source_start + other.len.to_u32() == self.source_start
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Spanned<T> {
    pub inner: T,
    pub location: SourceLocation,
}

impl<T> Spanned<T> {
    pub fn map<U>(self, f: impl Fn(T) -> U) -> Spanned<U> {
        f(self.inner).with_span(self.location)
    }
}

pub trait WithSpan {
    fn with_span(self, location: SourceLocation) -> Spanned<Self>
    where
        Self: Sized;
}

impl<T> WithSpan for T {
    #[inline]
    fn with_span(self, location: SourceLocation) -> Spanned<Self>
    where
        Self: Sized,
    {
        Spanned {
            inner: self,
            location,
        }
    }
}

struct LoadedSource {
    name: String,
    contents: String,
    source: Source,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct LineCol<'a> {
    pub name: &'a str,
    pub line: usize,
    pub col: usize,
}

#[derive(Default)]
pub struct SourceStore {
    files: Vec<LoadedSource>,
}

impl SourceStore {
    pub const fn new() -> Self {
        SourceStore { files: Vec::new() }
    }

    pub fn add(&mut self, name: &Path, source: &str) -> FileId {
        let id = self.files.len();
        self.files.push(LoadedSource {
            name: name.to_str().unwrap().to_owned(),
            contents: source.to_owned(),
            source: source.to_owned().into(),
        });

        FileId(id.to_u16().unwrap())
    }

    #[inline]
    pub fn name(&self, id: FileId) -> &str {
        &self.files[id.0.to_usize()].name
    }

    #[inline]
    pub fn source(&self, id: FileId) -> &Source {
        &self.files[id.0.to_usize()].source
    }

    #[inline]
    pub fn source_location_info(&self, loc: SourceLocation) -> LineCol {
        let source = self.source(loc.file_id);
        let name = self.name(loc.file_id);
        source
            .get_byte_line(loc.source_start.to_usize())
            .map(|(_, line, col)| LineCol {
                name,
                line: line + 1,
                col: col + 1,
            })
            .unwrap_or_default()
    }

    #[inline]
    pub fn get_str(&self, loc: SourceLocation) -> &str {
        let source = &self.files[loc.file_id.0.to_usize()].contents;
        let range = loc.start()..loc.end();
        &source[range]
    }
}

impl Cache<FileId> for &SourceStore {
    type Storage = String;

    #[inline]
    fn fetch(&mut self, id: &FileId) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        Ok(&self.files[id.0.to_usize()].source)
    }

    #[inline]
    fn display<'a>(&self, id: &'a FileId) -> Option<Box<dyn std::fmt::Display + 'a>> {
        let name = &self.files[id.0.to_usize()].name;

        Some(Box::new(name.clone()))
    }
}
