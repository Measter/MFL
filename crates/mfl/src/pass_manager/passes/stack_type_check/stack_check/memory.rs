use intcast::IntCast;
use smallvec::SmallVec;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    n_ops::{SliceNOps, VecNOps},
    pass_manager::PassManager,
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{TypeId, TypeKind},
        values::ValueId,
    },
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn extract_array(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    emit_array: bool,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 2);

    let [array_id, idx] = stack.popn().unwrap();
    let mut outputs = SmallVec::<[_; 2]>::new();

    if emit_array {
        let output_array = stores.values.new_value(op_loc, Some(array_id));
        outputs.push(output_array);
        stack.push(output_array);
    }

    let output_value = stores.values.new_value(op_loc, None);
    outputs.push(output_value);
    stack.push(output_value);

    stores.ops.set_op_io(op_id, &[array_id, idx], &outputs);
}

pub(crate) fn extract_struct(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    emit_struct: bool,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 1);

    let struct_id = stack.pop().unwrap();
    let mut outputs = SmallVec::<[_; 2]>::new();

    if emit_struct {
        let output_struct = stores.values.new_value(op_loc, Some(struct_id));
        outputs.push(output_struct);
        stack.push(output_struct);
    }

    let output_value = stores.values.new_value(op_loc, None);
    outputs.push(output_value);
    stack.push(output_value);

    stores.ops.set_op_io(op_id, &[struct_id], &outputs);
}

pub(crate) fn insert_array(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    emit_array: bool,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 2);

    let inputs = stack.popn::<3>().unwrap();
    let mut output = None;

    if emit_array {
        // Leave the array on the stack so the user can continue using it.
        let output_id = stores.values.new_value(op_loc, Some(inputs[1]));
        output = Some(output_id);
        stack.push(output_id);
    }

    stores.ops.set_op_io(op_id, &inputs, output.as_slice());
}

pub(crate) fn insert_struct(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    emit_struct: bool,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 2);

    let inputs = stack.popn::<2>().unwrap();
    let mut output = None;

    if emit_struct {
        let output_id = stores.values.new_value(op_loc, Some(inputs[1]));
        output = Some(output_id);
        stack.push(output_id);
    }

    stores.ops.set_op_io(op_id, &inputs, output.as_slice());
}

pub(crate) fn pack_array(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    count: u8,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, count.to_usize());

    let mut inputs = SmallVec::<[_; 8]>::new();
    let input_ids = stack.lastn(count.to_usize()).unwrap();
    for &id in input_ids {
        inputs.push(id);
    }

    stack.truncate(stack.len() - input_ids.len());

    let output = stores.values.new_value(op_loc, None);
    stack.push(output);
    stores.ops.set_op_io(op_id, &inputs, &[output]);
}

pub(crate) fn load(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 1);
    let input_value_id = stack.pop().unwrap();

    // We need to look up the type of our input to know how many values we create.
    // If it's a normal pointer, then it's one, if it's a function pointer then it's
    // however many values that function returns.
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        stores.ops.set_op_io(op_id, &[input_value_id], &[]);
        return;
    };

    let input_type_info = stores.types.get_type_info(input_type_id);
    let (input_count, output_count) = match input_type_info.kind {
        TypeKind::FunctionPointer => {
            let function_args = stores.types.get_function_pointer_args(input_type_info.id);
            (function_args.inputs.len(), function_args.outputs.len())
        }

        // We'll leave the full type checking up to the type checker, so the rest of the stack check
        // at least has a valid stack.
        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => (0, 1),
    };

    ensure_stack_depth(stores, had_error, stack, item_id, op_id, input_count);

    let mut inputs: SmallVec<[ValueId; 20]> = stack.drain(stack.len() - input_count..).collect();
    inputs.push(input_value_id);

    let mut outputs = SmallVec::<[_; 20]>::new();
    for _ in 0..output_count {
        let id = stores.values.new_value(op_loc, None);
        stack.push(id);
        outputs.push(id);
    }

    stores.ops.set_op_io(op_id, &inputs, &outputs);
}

pub(crate) fn store(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
) {
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 2);

    let inputs = stack.popn::<2>().unwrap();
    stores.ops.set_op_io(op_id, &inputs, &[]);
}

pub(crate) fn unpack(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 1);
    let input_value_id = stack.pop().unwrap();

    // To find out how any values we create, we need to look up the type of our input.
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        stores.ops.set_op_io(op_id, &[input_value_id], &[]);
        return;
    };

    let input_type_info = stores.types.get_type_info(input_type_id);
    let length = match input_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            if pass_manager
                .ensure_define_structs(stores, struct_item_id)
                .is_err()
            {
                stores.ops.set_op_io(op_id, &[input_value_id], &[]);
                had_error.set();

                0
            } else {
                stores.types.get_struct_def(input_type_id).fields.len()
            }
        }
        _ => {
            let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

            Diagnostic::error(op_loc, format!("unable to unpack a `{input_type_name}`"))
                .with_note("value must be an array or struct")
                .with_label_chain(input_value_id, 0, input_type_name)
                .attached(stores.diags, item_id);

            had_error.set();

            0
        }
    };

    let mut outputs = SmallVec::<[_; 20]>::new();

    for _ in 0..length {
        let id = stores.values.new_value(op_loc, None);
        stack.push(id);
        outputs.push(id);
    }

    stores.ops.set_op_io(op_id, &[input_value_id], &outputs);
}

pub(crate) fn pack_struct(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    target_type_id: TypeId,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    let type_info = stores.types.get_type_info(target_type_id);
    let (TypeKind::Struct(struct_item_id)
    | TypeKind::GenericStructInstance(struct_item_id)
    | TypeKind::GenericStructBase(struct_item_id)) = type_info.kind
    else {
        Diagnostic::error(op_loc, "cannot pack that type").attached(stores.diags, item_id);
        had_error.set();
        return;
    };

    if pass_manager
        .ensure_define_structs(stores, struct_item_id)
        .is_err()
    {
        stores.ops.set_op_io(op_id, &[], &[]);
        had_error.set();
    }

    let num_fields = match type_info.kind {
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            let struct_def = stores.types.get_struct_def(target_type_id);
            if struct_def.is_union {
                1
            } else {
                struct_def.fields.len()
            }
        }
        TypeKind::GenericStructBase(_) => {
            let struct_def = stores.types.get_generic_base_def(target_type_id);
            if struct_def.is_union {
                1
            } else {
                struct_def.fields.len()
            }
        }
        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::FunctionPointer
        | TypeKind::Bool => {
            unreachable!()
        }
    };

    ensure_stack_depth(stores, had_error, stack, item_id, op_id, num_fields);

    let mut inputs = SmallVec::<[_; 20]>::new();
    let input_value_ids = stack.lastn(num_fields).unwrap();
    for &input_value_id in input_value_ids {
        inputs.push(input_value_id);
    }

    stack.truncate(stack.len() - input_value_ids.len());

    let output = stores.values.new_value(op_loc, None);
    stack.push(output);
    stores.ops.set_op_io(op_id, &inputs, &[output]);
}
