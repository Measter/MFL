use intcast::IntCast;
use prettytable::{row, Table};
use smallvec::SmallVec;
use stores::items::ItemId;

use crate::{
    diagnostics::TABLE_FORMAT,
    error_signal::ErrorSignal,
    ir::{OpCode, TypeResolvedOp},
    pass_manager::{static_analysis::generate_type_mismatch_diag, PassManager},
    stores::{
        diagnostics::Diagnostic,
        item::ItemKind,
        ops::OpId,
        types::{BuiltinTypes, FloatWidth, IntKind, TypeId, TypeKind},
        values::ValueId,
    },
    Stores,
};

pub(crate) fn dup_over_rotate_swap_reverse(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let inputs: SmallVec<[ValueId; 20]> = op_data.inputs.as_slice().into();
    let outputs: SmallVec<[ValueId; 20]> = op_data.outputs.as_slice().into();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([input_type]) = stores.values.value_types([input]) else {
            continue;
        };
        stores.values.set_value_type(output, input_type);
    }
}

pub(crate) fn emit_stack(
    stores: &mut Stores,
    stack: &[ValueId],
    item_id: ItemId,
    op_id: OpId,
    show_labels: bool,
) {
    let mut note = Table::new();
    note.set_format(*TABLE_FORMAT);
    note.set_titles(row!["ID", "Type"]);

    let op_loc = stores.ops.get_token(op_id).location;
    let mut diag = Diagnostic::advice(op_loc, "stack trace");

    for (idx, value_id) in stack.iter().enumerate().rev() {
        let value_type = stores
            .values
            .value_types([*value_id])
            .map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });

        let value_idx = stack.len() - idx - 1;

        if show_labels {
            diag.add_label_chain(*value_id, value_idx.to_u64(), value_type);
        }

        note.add_row(row![value_idx.to_string(), value_type]);
    }

    diag.with_note(note.to_string())
        .attached(stores.diags, item_id);
}

pub(crate) fn push_bool(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(BuiltinTypes::Bool).id,
    );
}

pub(crate) fn push_int(stores: &mut Stores, op_id: OpId, int: IntKind) {
    let op_data = stores.ops.get_op_io(op_id);
    stores
        .values
        .set_value_type(op_data.outputs[0], stores.types.get_builtin(int.into()).id);
}

pub(crate) fn push_float(stores: &mut Stores, op_id: OpId, width: FloatWidth) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(width.into()).id,
    );
}

pub(crate) fn push_str(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let kind = stores.types.get_builtin(BuiltinTypes::String).id;
    stores.values.set_value_type(op_data.outputs[0], kind);
}

pub(crate) fn push_enum(stores: &mut Stores, op_id: OpId, enum_id: TypeId) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_type(op_data.outputs[0], enum_id)
}

pub(crate) fn function_pointer(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    callee_id: ItemId,
    params: &[TypeId],
) {
    let callee_header = stores.items.get_item_header(callee_id);

    let callee_id = if callee_header.kind == ItemKind::GenericFunction {
        if pass_manager
            .ensure_partially_resolve_types(stores, callee_id)
            .is_err()
        {
            had_error.set();
            return;
        }

        let Ok(new_id) =
            stores.get_generic_function_instance(pass_manager, had_error, callee_id, params)
        else {
            had_error.set();
            return;
        };

        // Need to overwrite to point at the correct new function ID.
        stores.ops.overwrite_type_resolved(
            op_id,
            OpCode::Complex(TypeResolvedOp::FunctionPointer {
                id: new_id,
                generic_params: Vec::new(),
            }),
        );

        new_id
    } else {
        callee_id
    };

    if pass_manager
        .ensure_type_resolved_signature(stores, callee_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let callee_sig = stores.sigs.trir.get_item_signature(callee_id);
    let function_pointer_type = stores.types.get_function_pointer(
        stores.strings,
        callee_sig.entry.clone(),
        callee_sig.exit.clone(),
    );

    let output_value_id = stores.ops.get_op_io(op_id).outputs[0];
    stores
        .values
        .set_value_type(output_value_id, function_pointer_type.id);
}

pub(crate) fn cast(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    target_id: TypeId,
) {
    let output_type_info = stores.types.get_type_info(target_id);
    match output_type_info.kind {
        TypeKind::Integer(int) => cast_to_int(stores, had_error, item_id, op_id, target_id, int),
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
            cast_to_ptr(stores, had_error, item_id, op_id, target_id)
        }
        TypeKind::Float(_) => cast_to_float(stores, had_error, item_id, op_id, target_id),
        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            let output_type_name = stores.strings.resolve(output_type_info.friendly_name);
            let op_loc = stores.ops.get_token(op_id).location;
            Diagnostic::error(op_loc, format!("cannot cast to `{output_type_name}`"))
                .attached(stores.diags, item_id);
            had_error.set();
        }
    }
}

fn cast_to_ptr(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    to_id: TypeId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Integer(IntKind::U64)
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_) => {}

        TypeKind::Integer(_) => {
            let input_type_name = stores.strings.resolve(input_type_info.friendly_name);
            let ptr_type_info = stores.types.get_type_info(to_id);
            let ptr_type_name = stores.strings.resolve(ptr_type_info.friendly_name);

            Diagnostic::error(
                op_token.location,
                format!("cannot cast `{input_type_name}` to `{ptr_type_name}`"),
            )
            .with_note("Can only cast u64 to pointers")
            .with_label_chain(input_value_id, 0, input_type_name)
            .attached(stores.diags, item_id);

            had_error.set();
        }

        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Float(_)
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    stores.values.set_value_type(op_data.outputs[0], to_id);
}

fn cast_to_int(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    to_id: TypeId,
    to_int: IntKind,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Bool | TypeKind::Float(_) | TypeKind::Integer(_) => {}
        TypeKind::Enum(_) => todo!(),
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
            if to_int != IntKind::U64 {
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);
                let output_type_info = stores.types.get_type_info(to_id);
                let output_type_name = stores.strings.resolve(output_type_info.friendly_name);

                Diagnostic::error(
                    op_token.location,
                    format!("cannot cast `{input_type_name}` to `{output_type_name}`"),
                )
                .with_label_chain(input_value_id, 0, input_type_name)
                .attached(stores.diags, item_id);

                had_error.set();
            }
        }

        TypeKind::Array { .. }
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::FunctionPointer => {
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    stores.values.set_value_type(op_data.outputs[0], to_id);
}

fn cast_to_float(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    to_id: TypeId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Integer(_) | TypeKind::Float(_) => {}

        TypeKind::Array { .. }
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    stores.values.set_value_type(op_data.outputs[0], to_id);
}
