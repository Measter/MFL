use std::fmt::Write;

use ariadne::{Color, Label};
use intcast::IntCast;
use prettytable::{row, Table};

use crate::{
    diagnostics::{self, TABLE_FORMAT},
    error_signal::ErrorSignal,
    ir::NameResolvedType,
    stores::{
        ops::OpId,
        source::SourceLocation,
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
    };
}

pub(super) fn failed_compare_stack_types(
    stores: &Stores,
    actual_stack: &[ValueId],
    expected_stack: &[TypeId],
    sample_location: SourceLocation,
    error_location: SourceLocation,
    msg: &str,
) {
    let mut note = Table::new();
    note.set_format(*TABLE_FORMAT);
    note.set_titles(row!("Depth", "Expected", "Actual"));

    let pairs = expected_stack.iter().zip(actual_stack).enumerate().rev();
    let mut bad_values = Vec::new();
    for (idx, (expected, actual_id)) in pairs {
        let value_type = stores
            .values
            .value_types([*actual_id])
            .map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });

        bad_values.push((*actual_id, idx.to_u64(), value_type));

        let expected_type_info = stores.types.get_type_info(*expected);
        let expected_name = stores.strings.resolve(expected_type_info.friendly_name);
        note.add_row(row!(
            (actual_stack.len() - idx - 1).to_string(),
            expected_name,
            value_type
        ));
    }

    let mut labels =
        diagnostics::build_creator_label_chain(stores, bad_values, Color::Yellow, Color::Cyan);
    labels.extend([
        Label::new(error_location)
            .with_color(Color::Red)
            .with_message("stack sampled here"),
        Label::new(sample_location)
            .with_color(Color::Cyan)
            .with_message("expected due to this signature"),
    ]);

    diagnostics::emit_error(stores, error_location, msg, labels, note.to_string());
}

pub(super) fn generate_type_mismatch_diag(
    stores: &Stores,
    operator_str: &str,
    op_id: OpId,
    types: &[ValueId],
) {
    let mut message = format!("cannot use `{operator_str}` on ");
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

    let mut bad_values = Vec::new();
    for (value_id, order) in types.iter().rev().zip(1..) {
        let value_type = stores
            .values
            .value_types([*value_id])
            .map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });
        bad_values.push((*value_id, order, value_type));
    }

    let mut labels =
        diagnostics::build_creator_label_chain(stores, bad_values, Color::Yellow, Color::Cyan);
    let op_loc = stores.ops.get_token(op_id).location;
    labels.push(Label::new(op_loc).with_color(Color::Red));
    diagnostics::emit_error(stores, op_loc, message, labels, None);
}

pub(super) fn generate_stack_length_mismatch_diag(
    stores: &Stores,
    sample_location: SourceLocation,
    error_location: SourceLocation,
    actual: usize,
    expected: usize,
    note: impl Into<Option<String>>,
) {
    let message = format!("expected {expected} items, found {actual}");

    let labels = if sample_location != error_location {
        let expected_suffix = if expected == 1 { "" } else { "s" };
        let actual_suffix = if actual == 1 { "" } else { "s" };
        vec![
            Label::new(sample_location)
                .with_color(Color::Cyan)
                .with_message(format!("{expected} value{expected_suffix} here...",))
                .with_order(1),
            Label::new(error_location)
                .with_color(Color::Red)
                .with_message(format!("... but found {actual} value{actual_suffix} here")),
        ]
    } else {
        vec![Label::new(error_location)
            .with_color(Color::Red)
            .with_message("here")]
    };

    diagnostics::emit_error(stores, sample_location, message, labels, note);
}
