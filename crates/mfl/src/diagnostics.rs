use ariadne::{Color, Label, Report, ReportKind};
use intcast::IntCast;
use lasso::Spur;
use once_cell::sync::Lazy;
use prettytable::format::{LinePosition, LineSeparator, TableFormat};

use crate::{
    error_signal::ErrorSignal,
    ir::StructDef,
    stores::{
        ops::OpId,
        source::{SourceLocation, Spanned},
        types::{TypeId, TypeInfo},
        values::ValueId,
    },
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

    diag.finish().eprint(&mut &*stores.source).unwrap();
}

pub struct NameCollision {
    pub prev: SourceLocation,
    pub new: SourceLocation,
}

pub fn handle_symbol_redef_error(
    stores: &Stores,
    had_error: &mut ErrorSignal,
    prev_def: Option<NameCollision>,
) {
    let Some(coll) = prev_def else {
        return;
    };

    had_error.set();
    emit_error(
        stores,
        coll.new,
        "item of that name already exists",
        [
            Label::new(coll.new).with_color(Color::Red),
            Label::new(coll.prev)
                .with_color(Color::Cyan)
                .with_message("previously defined here"),
        ],
        None,
    );
}

pub fn not_struct_error(
    stores: &mut Stores,
    input_struct_type_info: TypeInfo,
    input_struct_value_id: ValueId,
    op_id: OpId,
    error_str: &str,
) {
    let value_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);
    let mut labels = build_creator_label_chain(
        stores,
        [(input_struct_value_id, 1, value_type_name)],
        Color::Yellow,
        Color::Cyan,
    );
    let op_loc = stores.ops.get_token(op_id).location;
    labels.push(Label::new(op_loc).with_color(Color::Red));

    emit_error(
        stores,
        op_loc,
        format!("cannot {error_str} field from a `{value_type_name}`"),
        labels,
        None,
    );
}

pub fn field_not_found_error(
    stores: &mut Stores,
    field_name: Spanned<Spur>,
    struct_def: &StructDef<TypeId>,
    input_struct_type_info: TypeInfo,
    input_struct_value_id: ValueId,
) {
    let unknown_field_name = stores.strings.resolve(field_name.inner);
    let struct_name = stores.strings.resolve(struct_def.name.inner);

    let value_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);
    let mut labels = build_creator_label_chain(
        stores,
        [(input_struct_value_id, 1, value_type_name)],
        Color::Yellow,
        Color::Cyan,
    );

    labels.extend([
        Label::new(field_name.location).with_color(Color::Red),
        Label::new(struct_def.name.location)
            .with_color(Color::Cyan)
            .with_message("struct defined here"),
    ]);

    emit_error(
        stores,
        field_name.location,
        format!("unknown field `{unknown_field_name}` in struct `{struct_name}`"),
        labels,
        None,
    );
}
