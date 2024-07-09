use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    context::Context,
    diagnostics,
    ir::{Op, TypeResolvedOp},
    n_ops::{SliceNOps, VecNOps},
    pass_manager::{
        static_analysis::{Analyzer, ValueId},
        PassContext,
    },
    type_store::TypeKind,
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn extract_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_array: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let [array_id, idx] = stack.popn().unwrap();
    analyzer.consume_value(array_id, op.id);
    analyzer.consume_value(idx, op.id);

    let mut outputs = SmallVec::<[_; 2]>::new();

    if emit_array {
        let output_array = analyzer.new_value(op.token.location, Some(array_id));
        outputs.push(output_array);
        stack.push(output_array);
    }

    let output_value = analyzer.new_value(op.token.location, None);
    outputs.push(output_value);
    stack.push(output_value);

    analyzer.set_op_io(op, &[array_id, idx], &outputs);
}

pub(crate) fn extract_struct(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_struct: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 1);

    let struct_id = stack.pop().unwrap();
    analyzer.consume_value(struct_id, op.id);
    let mut outputs = SmallVec::<[_; 2]>::new();

    if emit_struct {
        let output_struct = analyzer.new_value(op.token.location, Some(struct_id));
        outputs.push(output_struct);
        stack.push(output_struct);
    }

    let output_value = analyzer.new_value(op.token.location, None);
    outputs.push(output_value);
    stack.push(output_value);

    analyzer.set_op_io(op, &[struct_id], &outputs);
}

pub(crate) fn insert_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_array: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<3>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    let mut output = None;
    if emit_array {
        // Leave the array on the stack so the user can continue using it.
        let output_id = analyzer.new_value(op.token.location, Some(inputs[1]));
        output = Some(output_id);
        stack.push(output_id);
    }

    analyzer.set_op_io(op, &inputs, output.as_slice());
}

pub(crate) fn insert_struct(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_struct: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    let mut output = None;
    if emit_struct {
        let output_id = analyzer.new_value(op.token.location, Some(inputs[1]));
        output = Some(output_id);
        stack.push(output_id);
    }

    analyzer.set_op_io(op, &inputs, output.as_slice());
}

pub(crate) fn pack_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    count: u8,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, count.to_usize());

    let mut inputs = SmallVec::<[_; 8]>::new();
    let input_ids = stack.lastn(count.to_usize()).unwrap();
    for &id in input_ids {
        inputs.push(id);
        analyzer.consume_value(id, op.id);
    }

    stack.truncate(stack.len() - input_ids.len());

    let output = analyzer.new_value(op.token.location, None);
    stack.push(output);
    analyzer.set_op_io(op, &inputs, &[output]);
}

pub(crate) fn store(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    analyzer.set_op_io(op, &inputs, &[]);
}

pub(crate) fn unpack(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 1);
    let input_value_id = stack.pop().unwrap();

    // To find out how any values we create, we need to look up the type of our input.
    let Some([input_type_id]) = analyzer.value_types([input_value_id]) else {
        analyzer.set_op_io(op, &[input_value_id], &[]);
        return;
    };

    let input_type_info = stores.types.get_type_info(input_type_id);
    let length = match input_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            if pass_ctx
                .ensure_define_structs(ctx, stores, struct_item_id)
                .is_err()
            {
                analyzer.set_op_io(op, &[input_value_id], &[]);
                *had_error = true;

                0
            } else {
                stores.types.get_struct_def(input_type_id).fields.len()
            }
        }
        _ => {
            let input_type_name = stores.strings.resolve(input_type_info.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(input_value_id, 0, input_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                format!("unable to unpack a `{input_type_name}`"),
                labels,
                "value must be an array or struct".to_owned(),
            );

            *had_error = true;

            0
        }
    };

    let mut outputs = SmallVec::<[_; 20]>::new();

    for _ in 0..length {
        let id = analyzer.new_value(op.token.location, None);
        stack.push(id);
        outputs.push(id);
    }

    analyzer.set_op_io(op, &[input_value_id], &outputs);
}
