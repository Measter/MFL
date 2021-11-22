use ariadne::{Color, Label, Report, ReportKind};

use crate::source_file::{SourceLocation, SourceStorage};

pub fn emit<Labels, Notes>(
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    notes: Notes,
    mut sources: &SourceStorage,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
    Notes: IntoIterator<Item = String>,
{
    let mut diag =
        Report::build(ReportKind::Error, loc.file_id, loc.source_start).with_message(msg);

    for note in notes {
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
