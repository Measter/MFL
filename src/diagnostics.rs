use ariadne::{Color, Label, Report, ReportKind};
use intcast::IntCast;

use crate::{
    program::static_analysis::{Analyzer, ValueId},
    source_file::{SourceLocation, SourceStorage},
};

pub fn build_creator_label_chain<'a, V>(
    analyzer: &Analyzer,
    values: V,
    root_color: Color,
    echo_color: Color,
) -> Vec<Label<SourceLocation>>
where
    V: IntoIterator<Item = (ValueId, u64, &'a str)>,
{
    let mut labels = Vec::new();

    for (vid, print_id, label) in values {
        let mut creators = analyzer.get_creator_token(vid);

        let root = creators.pop().unwrap();
        labels.push((
            Label::new(root.location)
                .with_color(root_color)
                .with_message(format!("{print_id}: {label}")),
            root.location,
        ));
        for creator in creators {
            labels.push((
                Label::new(creator.location)
                    .with_color(echo_color)
                    .with_message(format!("{print_id}: {label}")),
                creator.location,
            ));
        }
    }

    labels.sort_by_key(|(_, l)| *l);
    let num_labels = labels.len().to_i32().unwrap();
    labels
        .into_iter()
        .zip((0..num_labels).rev())
        .map(|((l, _), idx)| l.with_order(idx))
        .collect()
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
