use ariadne::{Color, Label, Report, ReportKind};

use crate::source_file::{SourceLocation, SourceStorage};

pub fn emit<Labels>(
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
    mut sources: &SourceStorage,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
{
    let mut diag =
        Report::build(ReportKind::Error, loc.file_id, loc.source_start).with_message(msg);

    if let Some(note) = note.into() {
        diag = diag.with_note(note);
    }

    for label in labels {
        diag = diag.with_label(label);
    }

    diag.finish().eprint(&mut sources).unwrap();
}

pub fn end_of_file(loc: SourceLocation, sources: &SourceStorage) {
    emit(
        loc,
        "unexpected end of file",
        Some(Label::new(loc).with_color(Color::Red)),
        None,
        sources,
    );
}
