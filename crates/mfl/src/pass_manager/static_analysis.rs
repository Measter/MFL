use std::fmt::Write;

use intcast::IntCast;
use lasso::Spur;
use prettytable::{row, Table};
use stores::{items::ItemId, source::SourceLocation};

use crate::{
    diagnostics::TABLE_FORMAT,
    error_signal::ErrorSignal,
    ir::NameResolvedType,
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{FloatWidth, IntKind, IntSignedness, TypeId},
        values::ValueId,
    },
    Stores,
};

use super::PassManager;

pub fn can_promote_int_unidirectional(from: IntKind, to: IntKind) -> bool {
    promote_int_type_uni_directional(from, to).is_some()
}

pub fn promote_int_type_uni_directional(from: IntKind, to: IntKind) -> Option<IntKind> {
    if from.signed == IntSignedness::Unsigned
        && to.signed == IntSignedness::Signed
        && to.width > from.width
    {
        Some((to.width, IntSignedness::Signed).into())
    } else if from.signed == to.signed && to.width >= from.width {
        Some((to.width, to.signed).into())
    } else {
        None
    }
}

pub fn can_promote_int_bidirectional(a: IntKind, b: IntKind) -> bool {
    promote_int_type_bidirectional(a, b).is_some()
}

pub fn promote_int_type_bidirectional(a: IntKind, b: IntKind) -> Option<IntKind> {
    promote_int_type_uni_directional(a, b).or_else(|| promote_int_type_uni_directional(b, a))
}

#[test]
fn test_promote_int() {
    use crate::stores::types::IntWidth::*;
    use IntSignedness::*;

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I16, Unsigned).into()),
        Some((I16, Unsigned,).into())
    );

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I32, Unsigned).into()),
        Some((I32, Unsigned).into())
    );

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I32, Signed).into()),
        Some((I32, Signed).into())
    );

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I16, Signed).into()),
        None
    );
    assert_eq!(
        promote_int_type_bidirectional((I16, Signed).into(), (I64, Unsigned).into()),
        None
    );
}

pub fn can_promote_float_unidirectional(from: FloatWidth, to: FloatWidth) -> bool {
    promote_float_unidirectional(from, to).is_some()
}

fn promote_float_unidirectional(from: FloatWidth, to: FloatWidth) -> Option<FloatWidth> {
    if to == FloatWidth::F64 || from == to {
        Some(to)
    } else {
        None
    }
}

pub(super) fn ensure_structs_declared_in_type(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    unresolved: &NameResolvedType,
) {
    match unresolved {
        NameResolvedType::SimpleCustom { id, .. } => {
            if pass_manager.ensure_declare_structs(stores, *id).is_err() {
                had_error.set();
            }
        }
        NameResolvedType::GenericInstance { id, params, .. } => {
            if pass_manager.ensure_declare_structs(stores, *id).is_err() {
                had_error.set();
            }
            for p in params {
                ensure_structs_declared_in_type(stores, pass_manager, had_error, p);
            }
        }
        NameResolvedType::SimpleBuiltin(_) | NameResolvedType::SimpleGenericParam(_) => {}
        NameResolvedType::Array(sub_type, _)
        | NameResolvedType::MultiPointer(sub_type)
        | NameResolvedType::SinglePointer(sub_type) => {
            ensure_structs_declared_in_type(stores, pass_manager, had_error, sub_type);
        }
        NameResolvedType::FunctionPointer { .. } => todo!(),
    };
}

pub(super) fn failed_compare_stack_types(
    stores: &mut Stores,
    item_id: ItemId,
    actual_stack: &[ValueId],
    expected_stack: &[TypeId],
    sample_location: SourceLocation,
    error_location: SourceLocation,
    msg: &str,
) {
    let mut diag = Diagnostic::error(error_location, msg)
        .primary_label_message("stack sampled here")
        .with_help_label(sample_location, "expected due to this signature");

    let mut note = Table::new();
    note.set_format(*TABLE_FORMAT);
    note.set_titles(row!("Depth", "Expected", "Actual"));

    let pairs = expected_stack.iter().zip(actual_stack).enumerate().rev();
    for (idx, (expected, actual_id)) in pairs {
        let value_type = stores
            .values
            .value_types([*actual_id])
            .map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });

        diag.add_label_chain(*actual_id, idx.to_u64(), value_type);

        let expected_type_info = stores.types.get_type_info(*expected);
        let expected_name = stores.strings.resolve(expected_type_info.friendly_name);
        note.add_row(row!(
            (actual_stack.len() - idx - 1).to_string(),
            expected_name,
            value_type
        ));
    }

    diag.with_note(note.to_string())
        .attached(stores.diags, item_id);
}

pub(super) fn generate_type_mismatch_diag(
    stores: &mut Stores,
    item_id: ItemId,
    operator_spur: Spur,
    op_id: OpId,
    types: &[ValueId],
) {
    let lexeme = stores.strings.resolve(operator_spur);
    let mut message = format!("cannot use `{lexeme}` on ");
    match types {
        [] => unreachable!(),
        [a] => {
            let kind = stores.values.value_types([*a]).map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });
            write!(&mut message, "`{kind}`").unwrap();
        }
        [a, b] => {
            let [a, b] = stores
                .values
                .value_types([*a, *b])
                .map_or(["Unknown", "Unknown"], |k| {
                    k.map(|id| {
                        let type_info = stores.types.get_type_info(id);
                        stores.strings.resolve(type_info.friendly_name)
                    })
                });
            write!(&mut message, "`{a}` and `{b}`").unwrap();
        }
        [xs @ .., last] => {
            for x in xs {
                let kind = stores.values.value_types([*x]).map_or("Unknown", |[v]| {
                    let type_info = stores.types.get_type_info(v);
                    stores.strings.resolve(type_info.friendly_name)
                });
                write!(&mut message, "`{kind}`, ").unwrap();
            }

            let kind = stores.values.value_types([*last]).map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });
            write!(&mut message, "and `{kind}`").unwrap();
        }
    }

    let op_loc = stores.ops.get_token(op_id).location;
    let mut diag = Diagnostic::error(op_loc, message);

    for (value_id, order) in types.iter().rev().zip(1..) {
        let value_type = stores
            .values
            .value_types([*value_id])
            .map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });
        diag.add_label_chain(*value_id, order, value_type);
    }

    diag.attached(stores.diags, item_id);
}

pub(super) fn generate_stack_length_mismatch_diag(
    stores: &mut Stores,
    item_id: ItemId,
    sample_location: SourceLocation,
    error_location: SourceLocation,
    actual: usize,
    expected: usize,
    note: impl Into<Option<String>>,
) {
    let message = format!("expected {expected} items, found {actual}");
    let mut diag = Diagnostic::error(sample_location, message);
    if let Some(note) = note.into() {
        diag.set_note(note);
    }

    if sample_location != error_location {
        let expected_suffix = if expected == 1 { "" } else { "s" };
        let actual_suffix = if actual == 1 { "" } else { "s" };
        diag = diag
            .primary_label_message(format!("... but found {actual} value{actual_suffix} here"))
            .with_help_label(
                sample_location,
                format!("{expected} value{expected_suffix} here...",),
            );
    } else {
        diag = diag.primary_label_message("here");
    };

    diag.attached(stores.diags, item_id);
}
