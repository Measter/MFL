use ariadne::{Color, Label, Report, ReportKind};
use intcast::IntCast;

use crate::{
    program::static_analysis::{Analyzer, ValueId},
    source_file::{SourceLocation, SourceStorage},
};

pub fn build_creator_label_chain(
    labels: &mut Vec<Label<SourceLocation>>,
    analyzer: &Analyzer,
    value_id: ValueId,
    print_id: u64,
    value_type: &str,
) {
    let mut creators = analyzer.get_creator_token(value_id);

    let root = creators.pop().unwrap();
    labels.push(
        Label::new(root.location)
            .with_color(Color::Yellow)
            .with_message(format!("{value_type} (id {print_id})")),
    );
    for creator in creators {
        labels.push(
            Label::new(creator.location)
                .with_color(Color::Cyan)
                .with_message(format!("{value_type} (id {print_id})")),
        );
    }
}

pub fn emit_error<Labels>(
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
    sources: &SourceStorage,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
{
    emit(ReportKind::Error, loc, msg, labels, note, sources)
}

pub fn emit_warning<Labels>(
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
    sources: &SourceStorage,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
{
    emit(ReportKind::Warning, loc, msg, labels, note, sources)
}

pub fn emit<Labels>(
    kind: ReportKind,
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
    mut sources: &SourceStorage,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
{
    let mut diag = Report::build(kind, loc.file_id, loc.source_start.to_usize()).with_message(msg);

    if let Some(note) = note.into() {
        diag = diag.with_note(note);
    }

    for label in labels {
        diag = diag.with_label(label);
    }

    diag.finish().eprint(&mut sources).unwrap();
}

pub fn end_of_file(loc: SourceLocation, sources: &SourceStorage) {
    emit_error(
        loc,
        "unexpected end of file",
        Some(Label::new(loc).with_color(Color::Red)),
        None,
        sources,
    );
}
