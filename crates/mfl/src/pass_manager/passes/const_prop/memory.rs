use std::fmt::Write;

use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    n_ops::SliceNOps,
    pass_manager::PassManager,
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{Integer, TypeId, TypeKind, TypeStore},
        values::{ConstVal, InitState, Offset},
    },
    Stores,
};

use super::{new_const_val_for_type, ConstFieldInitState};

fn write_const_val_to_variable(
    type_store: &mut TypeStore,
    state: &mut ConstVal,
    to_store_value: &ConstVal,
    cur_pointed_at_type: TypeId,
    mut offsets: std::slice::Iter<'_, Offset>,
) {
    if let Some(next) = offsets.next() {
        let var_type_info = type_store.get_type_info(cur_pointed_at_type);
        match var_type_info.kind {
            TypeKind::Array { type_id, .. } => {
                let ConstVal::Aggregate { sub_values } = state else {
                    unreachable!()
                };

                match next {
                    Offset::Unknown => {
                        // We are in an array, but don't know where in the array we are writing to.
                        // We should iterate over each index in the array, and write a final ConstVal::Unknown.
                        for sv in sub_values {
                            write_const_val_to_variable(
                                type_store,
                                sv,
                                &ConstVal::Unknown,
                                type_id,
                                offsets.clone(),
                            );
                        }
                    }
                    Offset::Known(offset) => {
                        write_const_val_to_variable(
                            type_store,
                            &mut sub_values[offset.to_usize()],
                            to_store_value,
                            type_id,
                            offsets,
                        );
                    }
                }
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let ConstVal::Aggregate { sub_values } = state else {
                    unreachable!()
                };

                let struct_def = type_store.get_struct_def(cur_pointed_at_type);
                let Offset::Known(offset) = next else {
                    panic!("ICE: struct field offset is unknown")
                };
                write_const_val_to_variable(
                    type_store,
                    &mut sub_values[offset.to_usize()],
                    to_store_value,
                    struct_def.fields[offset.to_usize()].kind.inner,
                    offsets,
                );
            }

            _ => unreachable!(),
        }
    } else {
        // No more offsets to go, we've reached the final destination
        *state = to_store_value.clone();
    }
}

pub(crate) fn index(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let [idx_value_id, array_value_id] = *op_data.inputs.as_arr();
    let output_value_id = op_data.outputs[0];
    let [ConstVal::Int(Integer::Unsigned(idx))] = stores.values.value_consts([idx_value_id]) else {
        // If we don't know the index, we should make sure that the pointer gets its offsets cleared,
        // as we no longer know where it's pointing.

        if let [ConstVal::Pointer {
            source_variable,
            offsets: Some(offsets),
        }] = stores.values.value_consts([array_value_id])
        {
            let mut new_offsets = offsets.clone();
            new_offsets.push(Offset::Unknown);

            stores.values.set_value_const(
                output_value_id,
                ConstVal::Pointer {
                    source_variable: *source_variable,
                    offsets: Some(new_offsets),
                },
            );
        }
        return;
    };

    let [array_type_id] = stores.values.value_types([array_value_id]).unwrap();
    let array_type_info = stores.types.get_type_info(array_type_id);

    let array_length = match array_type_info.kind {
        TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id) => {
            let info = stores.types.get_type_info(ptee_id);
            match info.kind {
                TypeKind::Array { length, .. } => length,
                // Don't handle structs
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
                TypeKind::Integer(_)
                | TypeKind::Float(_)
                | TypeKind::MultiPointer(_)
                | TypeKind::SinglePointer(_)
                | TypeKind::Bool
                | TypeKind::GenericStructBase(_)
                | TypeKind::Enum(_)
                | TypeKind::FunctionPointer => unreachable!(),
            }
        }
        TypeKind::Array { .. }
        | TypeKind::Struct(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => unreachable!(),
    };

    if idx.to_usize() >= array_length {
        let array_type_name = stores.strings.resolve(array_type_info.friendly_name);
        let idx_value = idx.to_string();
        let op_loc = stores.ops.get_token(op_id).location;

        Diagnostic::error(op_loc, "index out of bounds")
            .with_label_chain(array_value_id, 0, array_type_name)
            .with_label_chain(idx_value_id, 1, idx_value)
            .attached(stores.diags, item_id);

        had_error.set();

        // The index is invalid, so clear the offsets of the pointer.
        if let [ConstVal::Pointer {
            source_variable, ..
        }] = stores.values.value_consts([array_value_id])
        {
            stores.values.set_value_const(
                output_value_id,
                ConstVal::Pointer {
                    source_variable: *source_variable,
                    offsets: None,
                },
            );
        }

        return;
    }

    // Need to make sure we know exactly where the pointer is pointing.
    if let [ConstVal::Pointer {
        source_variable,
        offsets: Some(offsets),
    }] = stores.values.value_consts([array_value_id])
    {
        let mut new_offsets = offsets.clone();
        new_offsets.push(Offset::Known(*idx));
        stores.values.set_value_const(
            output_value_id,
            ConstVal::Pointer {
                source_variable: *source_variable,
                offsets: Some(new_offsets),
            },
        );
    }
}

pub(crate) fn field_access(stores: &mut Stores, field_name: Spur, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let struct_value_id = op_data.inputs[0];

    // Need to make sure we know exactly where the pointer is pointing.
    // If we don't then we can't do anything.
    let [ConstVal::Pointer {
        source_variable,
        offsets: Some(offsets),
    }] = stores.values.value_consts([struct_value_id])
    else {
        return;
    };

    let [struct_ptr_type_id] = stores.values.value_types([struct_value_id]).unwrap();
    let struct_ptr_type_info = stores.types.get_type_info(struct_ptr_type_id);

    let (TypeKind::MultiPointer(f) | TypeKind::SinglePointer(f)) = struct_ptr_type_info.kind else {
        unreachable!()
    };
    let struct_def = stores.types.get_struct_def(f);

    let new_idx = if struct_def.is_union {
        0
    } else {
        struct_def
            .fields
            .iter()
            .position(|f| f.name.inner == field_name)
            .unwrap()
            .to_u64()
    };

    let mut new_offsets = offsets.clone();
    new_offsets.push(Offset::Known(new_idx));
    let new_const_val = ConstVal::Pointer {
        source_variable: *source_variable,
        offsets: Some(new_offsets),
    };
    stores
        .values
        .set_value_const(op_data.outputs[0], new_const_val);
}

pub(crate) fn insert_array(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let output_value_id = op_data.outputs.first().copied();
    let &[inserted_value_id, array_value_id, idx_value_id] = op_data.inputs.as_slice() else {
        unreachable!()
    };

    let [input_array_type_id] = stores.values.value_types([array_value_id]).unwrap();
    let input_array_type_info = stores.types.get_type_info(input_array_type_id);

    let (array_type_id, array_length, is_ptr) = match input_array_type_info.kind {
        TypeKind::Array { length, .. } => (input_array_type_id, length, false),
        TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id) => {
            let info = stores.types.get_type_info(ptee_id);
            match info.kind {
                TypeKind::Array { length, .. } => (ptee_id, length, true),
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
                TypeKind::Integer(_)
                | TypeKind::Float(_)
                | TypeKind::MultiPointer(_)
                | TypeKind::SinglePointer(_)
                | TypeKind::Bool
                | TypeKind::GenericStructBase(_)
                | TypeKind::Enum(_)
                | TypeKind::FunctionPointer => unreachable!(),
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => unreachable!(),
    };

    let [ConstVal::Int(Integer::Unsigned(idx))] = stores.values.value_consts([idx_value_id]) else {
        // We don't know the index, so we should assume that it hits every index in the array.
        if is_ptr {
            // We need to overwrite every index in the pointer.
            let [inserted_value_type_id] = stores.values.value_types([inserted_value_id]).unwrap();
            let new_inserted_const_value = new_const_val_for_type(
                stores,
                pass_manager,
                had_error,
                inserted_value_type_id,
                ConstFieldInitState::Unknown,
            );

            let [input_array_const] = stores.values.value_consts([array_value_id]);
            let ConstVal::Pointer {
                source_variable,
                offsets: Some(offsets),
            } = input_array_const
            else {
                // Nothing we can do here.
                return;
            };

            let Some(variable_state) = variable_state.get_mut(source_variable) else {
                // It's a global variable, nothing to do.
                return;
            };

            let cur_pointed_at_type = stores.sigs.trir.get_variable_type(*source_variable);
            write_const_val_to_variable(
                stores.types,
                variable_state,
                &new_inserted_const_value,
                cur_pointed_at_type,
                offsets.iter(),
            );

            if let Some(output_value_id) = output_value_id {
                stores
                    .values
                    .set_value_const(output_value_id, input_array_const.clone());
            };
        } else if let Some(output_value_id) = output_value_id {
            // Clobber the entire array.
            let new_array_const_value = new_const_val_for_type(
                stores,
                pass_manager,
                had_error,
                input_array_type_id,
                ConstFieldInitState::Unknown,
            );

            stores
                .values
                .set_value_const(output_value_id, new_array_const_value);
        };

        return;
    };

    if idx.to_usize() >= array_length {
        let array_type_name = stores.strings.resolve(input_array_type_info.friendly_name);
        let idx_value = idx.to_string();
        let op_loc = stores.ops.get_token(op_id).location;

        Diagnostic::error(op_loc, "index out of bounds")
            .with_label_chain(array_value_id, 0, array_type_name)
            .with_label_chain(idx_value_id, 1, idx_value)
            .attached(stores.diags, item_id);

        had_error.set();

        if is_ptr {
            // The index is invalid, so clear the offsets of the pointer.
            if let [ConstVal::Pointer {
                source_variable, ..
            }] = stores.values.value_consts([array_value_id])
            {
                if let Some(output_value_id) = output_value_id {
                    stores.values.set_value_const(
                        output_value_id,
                        ConstVal::Pointer {
                            source_variable: *source_variable,
                            offsets: None,
                        },
                    );
                }
            }
        }

        return;
    }

    // We know the index.
    let [input_array_const] = stores.values.value_consts([array_value_id]);
    let [inserted_value_const] = stores.values.value_consts([inserted_value_id]);
    if is_ptr {
        let ConstVal::Pointer {
            source_variable,
            offsets: Some(offsets),
        } = input_array_const
        else {
            // Nothing we can do here.
            return;
        };

        let Some(variable_state) = variable_state.get_mut(source_variable) else {
            // It's a global variable, nothing to do.
            return;
        };

        let mut offsets = offsets.clone();
        offsets.push(Offset::Known(*idx));

        write_const_val_to_variable(
            stores.types,
            variable_state,
            inserted_value_const,
            array_type_id,
            offsets.iter(),
        );

        if let Some(output_value_id) = output_value_id {
            stores
                .values
                .set_value_const(output_value_id, input_array_const.clone());
        }
    } else if let Some(output_value_id) = output_value_id {
        let ConstVal::Aggregate { mut sub_values } = input_array_const.clone() else {
            // Nothing we can do here.
            return;
        };

        sub_values[idx.to_usize()] = inserted_value_const.clone();
        stores
            .values
            .set_value_const(output_value_id, ConstVal::Aggregate { sub_values });
    }
}

pub(crate) fn extract_array(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    // We might be outputting the array.

    let &[input_array_value_id, idx_value_id] = op_data.inputs.as_slice() else {
        unreachable!()
    };

    let extracted_value_id = match op_data.outputs() {
        [v] => *v,
        [output_array_value_id, extracted_value_id] => {
            let [input_array_const_val] = stores.values.value_consts([input_array_value_id]);
            stores
                .values
                .set_value_const(*output_array_value_id, input_array_const_val.clone());

            *extracted_value_id
        }
        _ => unreachable!(),
    };

    let [ConstVal::Int(Integer::Unsigned(idx))] = stores.values.value_consts([idx_value_id]) else {
        // We don't know the index, so magic up an unknown const value.
        let [extracted_type_id] = stores.values.value_types([extracted_value_id]).unwrap();
        let extracted_const_value = new_const_val_for_type(
            stores,
            pass_manager,
            had_error,
            extracted_type_id,
            ConstFieldInitState::Unknown,
        );

        stores
            .values
            .set_value_const(extracted_value_id, extracted_const_value);
        return;
    };

    let [input_array_type_id] = stores.values.value_types([input_array_value_id]).unwrap();
    let input_array_type_info = stores.types.get_type_info(input_array_type_id);

    let (array_length, is_ptr) = match input_array_type_info.kind {
        TypeKind::Array { length, .. } => (length, false),
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            // We don't know where we're extracting from, so magic up an unknown const.
            let [extracted_type_id] = stores.values.value_types([extracted_value_id]).unwrap();
            let extracted_const_value = new_const_val_for_type(
                stores,
                pass_manager,
                had_error,
                extracted_type_id,
                ConstFieldInitState::Unknown,
            );

            stores
                .values
                .set_value_const(extracted_value_id, extracted_const_value);

            return;
        }

        TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id) => {
            let info = stores.types.get_type_info(ptee_id);
            match info.kind {
                TypeKind::Array { length, .. } => (length, true),
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                    // We don't know where we're extracting from, so magic up an unknown const.
                    let [extracted_type_id] =
                        stores.values.value_types([extracted_value_id]).unwrap();
                    let extracted_const_value = new_const_val_for_type(
                        stores,
                        pass_manager,
                        had_error,
                        extracted_type_id,
                        ConstFieldInitState::Unknown,
                    );

                    stores
                        .values
                        .set_value_const(extracted_value_id, extracted_const_value);

                    return;
                }

                TypeKind::Integer(_)
                | TypeKind::Float(_)
                | TypeKind::MultiPointer(_)
                | TypeKind::SinglePointer(_)
                | TypeKind::Bool
                | TypeKind::GenericStructBase(_)
                | TypeKind::Enum(_)
                | TypeKind::FunctionPointer => unreachable!(),
            }
        }

        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => unreachable!(),
    };

    let [input_array_const] = stores.values.value_consts([input_array_value_id]);
    let extracted_const_value = 'get_const_val: {
        if idx.to_usize() >= array_length {
            let array_type_name = stores.strings.resolve(input_array_type_info.friendly_name);
            let idx_value = idx.to_string();
            let op_loc = stores.ops.get_token(op_id).location;

            Diagnostic::error(op_loc, "index out of bounds")
                .with_label_chain(input_array_value_id, 0, array_type_name)
                .with_label_chain(idx_value_id, 1, idx_value)
                .attached(stores.diags, item_id);

            had_error.set();
            None
        } else if is_ptr {
            let ConstVal::Pointer {
                source_variable,
                offsets: Some(offsets),
            } = input_array_const
            else {
                // Pointer has invalid offsets, nothing else to do.
                break 'get_const_val None;
            };

            let Some(mut cur_state) = variable_state.get(source_variable) else {
                // It's a global variable, so magic up an unknown value.
                break 'get_const_val None;
            };

            let mut cur_pointed_at_type = stores.sigs.trir.get_variable_type(*source_variable);
            let mut offsets = offsets.to_owned();
            offsets.push(Offset::Known(*idx));
            for offset in offsets {
                let Offset::Known(offset) = offset else {
                    // We hit an unknown offset, which means we don't know which element of an array we're going into.
                    // We'll just magic out a new unknown state for the final type.
                    break 'get_const_val None;
                };

                let var_type_info = stores.types.get_type_info(cur_pointed_at_type);
                match var_type_info.kind {
                    TypeKind::Array { type_id, .. } => {
                        cur_pointed_at_type = type_id;
                        let ConstVal::Aggregate { sub_values } = cur_state else {
                            unreachable!()
                        };

                        cur_state = &sub_values[offset.to_usize()];
                    }
                    TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                        let struct_def = stores.types.get_struct_def(cur_pointed_at_type);
                        let field = &struct_def.fields[offset.to_usize()];
                        cur_pointed_at_type = field.kind.inner;
                        let ConstVal::Aggregate { sub_values } = cur_state else {
                            unreachable!()
                        };

                        cur_state = &sub_values[offset.to_usize()];
                    }

                    _ => unreachable!(),
                }
            }

            Some(cur_state.clone())
        } else {
            // We're dealing with an array on the value stack.
            let ConstVal::Aggregate { sub_values } = input_array_const else {
                unreachable!()
            };

            Some(sub_values[idx.to_usize()].clone())
        }
    };

    let extracted_const_value = extracted_const_value.unwrap_or_else(|| {
        // If we couldn't extract a valid one, magic up an Unknown
        let [extracted_type_id] = stores.values.value_types([extracted_value_id]).unwrap();
        new_const_val_for_type(
            stores,
            pass_manager,
            had_error,
            extracted_type_id,
            ConstFieldInitState::Unknown,
        )
    });

    stores
        .values
        .set_value_const(extracted_value_id, extracted_const_value);
}

pub(crate) fn insert_struct(
    stores: &mut Stores,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    op_id: OpId,
    field_name: Spur,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let output_value_id = op_data.outputs.first().copied();
    let &[inserted_value_id, input_struct_value_id] = op_data.inputs.as_slice() else {
        unreachable!()
    };

    let [input_struct_type_id] = stores.values.value_types([input_struct_value_id]).unwrap();
    let input_struct_type_info = stores.types.get_type_info(input_struct_type_id);

    let (struct_type_id, is_ptr) = match input_struct_type_info.kind {
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => (input_struct_type_id, false),

        TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id) => {
            let info = stores.types.get_type_info(ptee_id);
            match info.kind {
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => (ptee_id, true),

                TypeKind::Array { .. }
                | TypeKind::Integer(_)
                | TypeKind::Float(_)
                | TypeKind::MultiPointer(_)
                | TypeKind::SinglePointer(_)
                | TypeKind::Bool
                | TypeKind::GenericStructBase(_)
                | TypeKind::Enum(_)
                | TypeKind::FunctionPointer => unreachable!(),
            }
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::FunctionPointer
        | TypeKind::Bool
        | TypeKind::Enum(_)
        | TypeKind::GenericStructBase(_) => {
            unreachable!()
        }
    };

    let struct_def = stores.types.get_struct_def(struct_type_id);
    let field_idx = struct_def
        .fields
        .iter()
        .position(|f| f.name.inner == field_name)
        .unwrap();

    let [inserted_value_const_value, input_struct_const_value] = stores
        .values
        .value_consts([inserted_value_id, input_struct_value_id]);

    let output_const_value = if is_ptr {
        let ConstVal::Pointer {
            source_variable,
            offsets: Some(offsets),
        } = input_struct_const_value
        else {
            // Nothing we can do here.
            return;
        };

        let Some(variable_state) = variable_state.get_mut(source_variable) else {
            // It's a global variable, nothing to do.
            return;
        };

        let mut offsets = offsets.clone();
        offsets.push(Offset::Known(field_idx.to_u64()));

        write_const_val_to_variable(
            stores.types,
            variable_state,
            inserted_value_const_value,
            struct_type_id,
            offsets.iter(),
        );

        input_struct_const_value.clone()
    } else {
        let ConstVal::Aggregate { mut sub_values } = input_struct_const_value.clone() else {
            unreachable!()
        };

        sub_values[field_idx] = inserted_value_const_value.clone();
        ConstVal::Aggregate { sub_values }
    };

    if let Some(output_value_id) = output_value_id {
        stores
            .values
            .set_value_const(output_value_id, output_const_value);
    }
}

pub(crate) fn load(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let output_value_id = op_data.outputs[0];
    let var_value_id = op_data.inputs[0];
    let [var_const_value] = stores.values.value_consts([var_value_id]);

    let ConstVal::Pointer {
        source_variable,
        offsets: Some(offsets),
    } = var_const_value
    else {
        return;
    };

    let source_variable = *source_variable;

    let Some(var_state) = variable_state.get(&source_variable) else {
        // It's a global variable, we can't handle those.
        // We'll just assume the value is initialized with Unknown.
        let [output_type_id] = stores.values.value_types([output_value_id]).unwrap();
        let new_const_val = new_const_val_for_type(
            stores,
            pass_manager,
            had_error,
            output_type_id,
            ConstFieldInitState::Unknown,
        );

        stores
            .values
            .set_value_const(output_value_id, new_const_val);

        return;
    };

    let mut cur_pointed_at_type = stores.sigs.trir.get_variable_type(source_variable);
    let mut cur_state = var_state;
    let mut note_location = String::new();
    for &offset in offsets {
        let Offset::Known(offset) = offset else {
            // We hit an unknown offset, which means we don't know which element of an array we're going into.
            // We'll just magic out a new unknown state for the final type.
            // Might be worth pursuing a merging of sub-states in the array?
            let [output_type_id] = stores.values.value_types([output_value_id]).unwrap();

            let new_const_val = new_const_val_for_type(
                stores,
                pass_manager,
                had_error,
                output_type_id,
                ConstFieldInitState::Unknown,
            );

            stores
                .values
                .set_value_const(output_value_id, new_const_val);

            return;
        };

        let var_type_info = stores.types.get_type_info(cur_pointed_at_type);
        match var_type_info.kind {
            TypeKind::Array { type_id, .. } => {
                cur_pointed_at_type = type_id;
                let ConstVal::Aggregate { sub_values } = cur_state else {
                    unreachable!()
                };

                write!(&mut note_location, "[{offset}]").unwrap();
                cur_state = &sub_values[offset.to_usize()];
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_def = stores.types.get_struct_def(cur_pointed_at_type);
                let field = &struct_def.fields[offset.to_usize()];
                cur_pointed_at_type = field.kind.inner;
                let ConstVal::Aggregate { sub_values } = cur_state else {
                    unreachable!()
                };

                let field_name = stores.strings.resolve(field.name.inner);
                write!(&mut note_location, ".{field_name}").unwrap();
                cur_state = &sub_values[offset.to_usize()];
            }

            _ => unreachable!(),
        }
    }

    let init_state = cur_state.get_init_state();
    if init_state != InitState::Full {
        let var_header = stores.items.get_item_header(source_variable);
        let op_loc = stores.ops.get_token(op_id);

        let (primary_msg_chunk, note_msg_chunk) = match init_state {
            InitState::Full => unreachable!(),
            InitState::Partial => ("partially ", "fully "),
            InitState::None => ("un", ""),
        };

        let mut diag = Diagnostic::error(
            op_loc.location,
            format!("read from {primary_msg_chunk}initialized memory"),
        )
        .primary_label_message("read occurred here")
        .with_label_chain(var_value_id, 0, "variable pointer")
        .with_help_label(var_header.name.location, "variable defined here");

        if !offsets.is_empty() {
            // We're pointing into sub-sections of the aggregate.
            let item_header = stores.items.get_item_header(source_variable);
            let var_name = stores.strings.resolve(item_header.name.inner);
            diag.set_note(format!(
                "Tried to access sub-element {var_name}{note_location} which is not {note_msg_chunk}initialized"
            ));
        }

        diag.attached(stores.diags, item_id);

        had_error.set();
    }

    stores
        .values
        .set_value_const(output_value_id, cur_state.clone());
}

pub(crate) fn store(
    stores: &mut Stores,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr();
    let [data_const_val, var_const_value] = stores.values.value_consts(input_value_ids);

    let ConstVal::Pointer {
        source_variable,
        offsets: Some(offsets),
    } = var_const_value
    else {
        return;
    };

    let Some(state) = variable_state.get_mut(source_variable) else {
        // It's a global variable, we can't handle those.
        return;
    };

    let cur_pointed_at_type = stores.sigs.trir.get_variable_type(*source_variable);
    write_const_val_to_variable(
        stores.types,
        state,
        data_const_val,
        cur_pointed_at_type,
        offsets.iter(),
    );
}

pub(crate) fn pack_enum(stores: &mut Stores, op_id: OpId, enum_id: TypeId) {
    let op_data = stores.ops.get_op_io(op_id);
    let discrim_value_id = op_data.inputs[0];
    let [discrim_const_val] = stores.values.value_consts([discrim_value_id]);

    let ConstVal::Int(Integer::Unsigned(i)) = discrim_const_val else {
        return;
    };

    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_const(
        op_data.outputs[0],
        ConstVal::Enum(enum_id, i.to_u16().unwrap()),
    );
}

pub(crate) fn pack_struct_and_array(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let mut values = Vec::new();

    for &input in &op_data.inputs {
        let [input_const] = stores.values.value_consts([input]);
        values.push(input_const.clone());
    }

    stores.values.set_value_const(
        op_data.outputs[0],
        ConstVal::Aggregate { sub_values: values },
    );
}

pub(crate) fn init_local(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    variable_id: ItemId,
) {
    let var_type = stores.sigs.trir.get_variable_type(variable_id);

    *variable_state.get_mut(&variable_id).unwrap() = new_const_val_for_type(
        stores,
        pass_manager,
        had_error,
        var_type,
        ConstFieldInitState::Unknown,
    );
}
