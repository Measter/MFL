use ariadne::{Color, Label, Report, ReportKind};
use intcast::IntCast;
use once_cell::sync::Lazy;
use prettytable::format::{LinePosition, LineSeparator, TableFormat};

use crate::{
    stores::{values::ValueId, source::SourceLocation},
    Stores,
};

pub static TABLE_FORMAT: Lazy<TableFormat> = Lazy::new(|| {
    let mut format = TableFormat::new();
    format.padding(1, 1);
    format.column_separator('│');
    format.separators(
        &[LinePosition::Title],
        LineSeparator::new('─', '┼', '├', '┤'),
    );
    format
});

pub fn build_creator_label_chain<'a, V>(
    stores: &Stores,
    values: V,
    root_color: Color,
    echo_color: Color,
) -> Vec<Label<SourceLocation>>
where
    V: IntoIterator<Item = (ValueId, u64, &'a str)>,
{
    let mut labels = Vec::new();

    for (vid, print_id, label) in values {
        let mut creators = stores.values.get_creator_token(vid);

        let root = creators.pop().unwrap();
        labels.push((
            Label::new(root)
                .with_color(root_color)
                .with_message(format!("{print_id}: {label}")),
            root,
        ));
        for creator in creators {
            labels.push((
                Label::new(creator)
                    .with_color(echo_color)
                    .with_message(format!("{print_id}: {label}")),
                creator,
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
    stores: &Stores,
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
{
    emit(stores, ReportKind::Error, loc, msg, labels, note);
}

pub fn emit_warning<Labels>(
    stores: &Stores,
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
) where
    Labels: IntoIterator<Item = Label<SourceLocation>>,
{
    emit(stores, ReportKind::Warning, loc, msg, labels, note);
}

pub fn emit<Labels>(
    stores: &Stores,
    kind: ReportKind,
    loc: SourceLocation,
    msg: impl ToString,
    labels: Labels,
    note: impl Into<Option<String>>,
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

    diag.finish().eprint(&mut &stores.source).unwrap();
}
