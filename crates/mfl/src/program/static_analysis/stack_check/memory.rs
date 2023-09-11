use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    diagnostics,
    n_ops::{SliceNOps, VecNOps},
    opcode::Op,
    type_store::{TypeId, TypeKind},
    Stores,
};

use super::{
    super::{Analyzer, ValueId},
    ensure_stack_depth,
};

pub fn pack_array(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
    count: u8,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, count.to_usize());

    let mut inputs = Vec::new();
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

pub fn pack_struct(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
    type_id: TypeId,
) {
    let type_info = stores.types.get_type_info(type_id);
    let num_fields = match type_info.kind {
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            let struct_def = stores.types.get_struct_def(type_id);
            if struct_def.is_union {
                1
            } else {
                struct_def.fields.len()
            }
        }
        TypeKind::GenericStructBase(_) => {
            let struct_def = stores.types.get_generic_base_def(type_id);
            if struct_def.is_union {
                1
            } else {
                struct_def.fields.len()
            }
        }
        _ => {
            diagnostics::emit_error(
                stores,
                op.token.location,
                "cannot pack that type",
                [Label::new(op.token.location).with_color(Color::Red)],
                None,
            );
            *had_error = true;
            return;
        }
    };

    ensure_stack_depth(stores, analyzer, had_error, stack, op, num_fields);

    let mut inputs = Vec::new();
    let input_ids = stack.lastn(num_fields).unwrap();
    for &id in input_ids {
        inputs.push(id);
        analyzer.consume_value(id, op.id);
    }

    stack.truncate(stack.len() - input_ids.len());

    let output = analyzer.new_value(op.token.location, None);
    stack.push(output);
    analyzer.set_op_io(op, &inputs, &[output]);
}

pub fn extract_array(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
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

pub fn insert_array(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
    emit_array: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<3>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    let mut outputs = SmallVec::<[_; 1]>::new();

    if emit_array {
        // Leave the array on the stack so the user can continue using it.
        let output = analyzer.new_value(op.token.location, Some(inputs[1]));
        outputs.push(output);
        stack.push(output);
    }

    analyzer.set_op_io(op, &inputs, &outputs);
}

pub fn insert_struct(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
    emit_struct: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    let mut outputs = SmallVec::<[_; 1]>::new();
    if emit_struct {
        // Leave the struct on the stack so the user can continue using it.
        let output = analyzer.new_value(op.token.location, Some(inputs[1]));
        outputs.push(output);
        stack.push(output);
    }

    analyzer.set_op_io(op, &inputs, &outputs);
}

pub fn extract_struct(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
    emit_struct: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 1);

    let [struct_id] = stack.popn().unwrap();
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

pub fn unpack(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 1);
    let input_id = stack.pop().unwrap();

    // To find out how many values we create, we need to look up the type of our input.
    let Some([input_type_id]) = analyzer.value_types([input_id]) else {
        analyzer.set_op_io(op, &[input_id], &[]);
        return;
    };

    let input_type_info = stores.types.get_type_info(input_type_id);

    let length = match input_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            let struct_info = stores.types.get_struct_def(input_type_id);
            struct_info.fields.len()
        }
        _ => {
            *had_error = true;
            let value_type_name = stores.strings.resolve(input_type_info.name);
            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(input_id, 0, value_type_name)],
                Color::Yellow,
                Color::Cyan,
            );

            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                format!("unable to unpack a `{value_type_name}`",),
                labels,
                "value must be an array or struct".to_owned(),
            );
            0
        }
    };

    let mut outputs = Vec::new();

    for _ in 0..length {
        let id = analyzer.new_value(op.token.location, None);
        stack.push(id);
        outputs.push(id);
    }

    analyzer.set_op_io(op, &[input_id], &outputs);
}

pub fn store(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    analyzer.set_op_io(op, &inputs, &[]);
}
