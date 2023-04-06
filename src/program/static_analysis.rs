use std::{
    fmt::{Display, Write},
    ops::Not,
};

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::HashMapNOps,
    opcode::{IntKind, Op, OpCode, OpId},
    option::OptionExt,
    program::{ItemId, Program},
    source_file::{SourceLocation, SourceStorage},
    type_store::{IntWidth, Signedness, TypeId, TypeKind, TypeStore},
};

use self::stack_check::{eat_one_make_one, eat_two_make_one, make_one};

mod const_prop;
mod stack_check;
mod type_check2;

fn can_promote_int_unidirectional(
    from_width: IntWidth,
    from_signed: Signedness,
    to_width: IntWidth,
    to_signed: Signedness,
) -> bool {
    promote_int_type_uni_directional(from_width, from_signed, to_width, to_signed).is_some()
}

pub fn promote_int_type_uni_directional(
    from_width: IntWidth,
    from_signed: Signedness,
    to_width: IntWidth,
    to_signed: Signedness,
) -> Option<(Signedness, IntWidth)> {
    if from_signed == Signedness::Unsigned
        && to_signed == Signedness::Signed
        && to_width > from_width
    {
        Some((Signedness::Signed, to_width))
    } else if from_signed == to_signed && to_width >= from_width {
        Some((to_signed, to_width))
    } else {
        None
    }
}

fn can_promote_int_bidirectional(
    a_width: IntWidth,
    a_signed: Signedness,
    b_width: IntWidth,
    b_signed: Signedness,
) -> bool {
    promote_int_type_bidirectional(a_width, a_signed, b_width, b_signed).is_some()
}

pub fn promote_int_type_bidirectional(
    a_width: IntWidth,
    a_signed: Signedness,
    b_width: IntWidth,
    b_signed: Signedness,
) -> Option<(Signedness, IntWidth)> {
    promote_int_type_uni_directional(a_width, a_signed, b_width, b_signed)
        .or_else(|| promote_int_type_uni_directional(b_width, b_signed, a_width, a_signed))
}

#[test]
fn test_promote_int() {
    use IntWidth::*;
    use Signedness::*;

    assert_eq!(
        promote_int_type_bidirectional(I16, Unsigned, I16, Unsigned),
        Some((Unsigned, I16))
    );

    assert_eq!(
        promote_int_type_bidirectional(I16, Unsigned, I32, Unsigned),
        Some((Unsigned, I32))
    );

    assert_eq!(
        promote_int_type_bidirectional(I16, Unsigned, I32, Signed),
        Some((Signed, I32))
    );

    assert_eq!(
        promote_int_type_bidirectional(I16, Unsigned, I16, Signed),
        None
    );
    assert_eq!(
        promote_int_type_bidirectional(I16, Signed, I64, Unsigned),
        None
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtrId {
    Mem(ItemId),
    Str(Spur),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstVal {
    Int(IntKind),
    Bool(bool),
    Ptr {
        id: PtrId,
        src_op_loc: SourceLocation,
        offset: Option<u64>,
    },
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueId(u16);

impl Display for ValueId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VId")?;
        self.0.fmt(f)?;
        f.write_char('_')
    }
}

#[derive(Debug, Clone)]
struct Value {
    source_location: SourceLocation,
    parent_value: Option<ValueId>,
    consumer: SmallVec<[OpId; 4]>,
}

#[derive(Debug, Clone)]
pub struct OpData {
    #[allow(unused)] // We need this for a debug print in a panic.
    creator_token: Token,
    inputs: SmallVec<[ValueId; 8]>,
    outputs: SmallVec<[ValueId; 8]>,
}

impl OpData {
    pub fn inputs(&self) -> &[ValueId] {
        self.inputs.as_ref()
    }

    pub fn outputs(&self) -> &[ValueId] {
        self.outputs.as_ref()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IfMerge {
    pub then_value: ValueId,
    pub else_value: ValueId,
    pub output_value: ValueId,
}

#[derive(Debug, Clone, Copy)]
pub struct WhileMerge {
    pub pre_value: ValueId,
    pub condition_value: ValueId,
}

#[derive(Debug, Clone)]
pub struct WhileMerges {
    pub condition: SmallVec<[WhileMerge; 4]>,
    pub body: SmallVec<[WhileMerge; 4]>,
}

#[derive(Debug, Clone, Default)]
pub struct Analyzer {
    value_lifetime: HashMap<ValueId, Value>,
    value_types: HashMap<ValueId, TypeId>,
    value_consts: HashMap<ValueId, ConstVal>,

    op_if_merges: HashMap<OpId, Vec<IfMerge>>,
    op_while_merges: HashMap<OpId, WhileMerges>,

    op_io_data: HashMap<OpId, OpData>,
}

impl Analyzer {
    fn new_value(
        &mut self,
        source_location: SourceLocation,
        parent_value: Option<ValueId>,
    ) -> ValueId {
        let id = self.value_lifetime.len();
        let id = ValueId(id.to_u16().unwrap());

        let value_exists = self
            .value_lifetime
            .insert(
                id,
                Value {
                    source_location,
                    parent_value,
                    consumer: SmallVec::new(),
                },
            )
            .is_some();

        if value_exists {
            panic!("ICE: Created value with duplicate ID: {id:?}");
        };

        id
    }

    fn values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.value_lifetime[&id])
    }

    fn consume_value(&mut self, value: ValueId, consumer_id: OpId) {
        let val = self.value_lifetime.get_mut(&value).unwrap();
        val.consumer.push(consumer_id);
    }

    pub fn value_types<const N: usize>(&self, ids: [ValueId; N]) -> Option<[TypeId; N]> {
        self.value_types.get_n(ids)
    }

    fn set_value_type(&mut self, id: ValueId, kind: TypeId) {
        self.value_types
            .insert(id, kind)
            .expect_none("ICE: Tried to set a value type twice");
    }

    pub fn value_consts<const N: usize>(&self, ids: [ValueId; N]) -> Option<[ConstVal; N]> {
        self.value_consts.get_n(ids)
    }

    pub fn set_value_const(&mut self, id: ValueId, const_val: ConstVal) {
        self.value_consts
            .insert(id, const_val)
            .expect_none("ICE: Tried to overwrite const value");
    }

    fn clear_value_const(&mut self, id: ValueId) {
        self.value_consts.remove(&id);
    }

    fn set_if_merges(&mut self, op: &Op, merges: Vec<IfMerge>) {
        self.op_if_merges
            .insert(op.id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    fn set_while_merges(&mut self, op: &Op, merges: WhileMerges) {
        self.op_while_merges
            .insert(op.id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    pub fn get_if_merges(&self, op_id: OpId) -> Option<&Vec<IfMerge>> {
        self.op_if_merges.get(&op_id)
    }

    pub fn get_while_merges(&self, op_id: OpId) -> Option<&WhileMerges> {
        self.op_while_merges.get(&op_id)
    }

    #[track_caller]
    fn set_op_io(&mut self, op: &Op, inputs: &[ValueId], outputs: &[ValueId]) {
        let new_data = OpData {
            creator_token: op.token,
            inputs: inputs.into(),
            outputs: outputs.into(),
        };
        if let Some(prev) = self.op_io_data.get(&op.id) {
            panic!("Set operands twice - cur_token: {op:#?}, new_data: {new_data:#?}, prev_data: {prev:#?}");
        }
        self.op_io_data.insert(op.id, new_data);
    }

    #[track_caller]
    pub fn get_op_io(&self, op_idx: OpId) -> &OpData {
        &self.op_io_data[&op_idx]
    }

    /// Returns the creator token of a value, treating Dup and Over tokens as transparent.
    pub fn get_creator_token(&self, value_id: ValueId) -> SmallVec<[SourceLocation; 2]> {
        let mut creators = SmallVec::new();

        let value_info = &self.value_lifetime[&value_id];
        let mut cur_creator = value_info.parent_value;
        creators.push(value_info.source_location);

        while let Some(parent) = cur_creator {
            let value_info = &self.value_lifetime[&parent];
            cur_creator = value_info.parent_value;
            creators.push(value_info.source_location);
        }

        creators
    }
}

fn failed_compare_stack_types(
    analyzer: &Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    actual_stack: &[ValueId],
    expected_stack: &[TypeId],
    sample_location: SourceLocation,
    error_location: SourceLocation,
    msg: &str,
) {
    let mut note = "\n\t\tDepth | Expected |   Actual\n\
        \t\t______|__________|_________"
        .to_owned();

    let pairs = expected_stack.iter().zip(actual_stack).enumerate().rev();
    let mut bad_values = Vec::new();
    for (idx, (expected, actual_id)) in pairs {
        let value_type = analyzer.value_types([*actual_id]).map_or("Unknown", |[v]| {
            let type_info = type_store.get_type_info(v);
            interner.resolve_lexeme(type_info.name)
        });

        bad_values.push((*actual_id, idx.to_u64(), value_type));

        let expected_type_info = type_store.get_type_info(*expected);
        let expected_name = interner.resolve_lexeme(expected_type_info.name);
        write!(
            &mut note,
            "\n\t\t{:<5} | {:<8} | {:>8}",
            actual_stack.len() - idx - 1,
            expected_name,
            value_type,
        )
        .unwrap();
    }

    let mut labels =
        diagnostics::build_creator_label_chain(analyzer, bad_values, Color::Yellow, Color::Cyan);
    labels.extend([
        Label::new(error_location)
            .with_color(Color::Red)
            .with_message("stack sampled here"),
        Label::new(sample_location)
            .with_color(Color::Cyan)
            .with_message("expected due to this signature"),
    ]);

    diagnostics::emit_error(error_location, msg, labels, note, source_store);
}

fn generate_type_mismatch_diag(
    analyzer: &Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    operator_str: &str,
    op: &Op,
    types: &[ValueId],
) {
    let mut message = format!("cannot use `{operator_str}` on ");
    match types {
        [] => unreachable!(),
        [a] => {
            let kind = analyzer.value_types([*a]).map_or("Unknown", |[v]| {
                let type_info = type_store.get_type_info(v);
                interner.resolve_lexeme(type_info.name)
            });
            write!(&mut message, "`{kind}`").unwrap();
        }
        [a, b] => {
            let [a, b] = analyzer
                .value_types([*a, *b])
                .map_or(["Unknown", "Unknown"], |k| {
                    k.map(|id| {
                        let type_info = type_store.get_type_info(id);
                        interner.resolve_lexeme(type_info.name)
                    })
                });
            write!(&mut message, "`{a}` and `{b}`").unwrap()
        }
        [xs @ .., last] => {
            for x in xs {
                let kind = analyzer.value_types([*x]).map_or("Unknown", |[v]| {
                    let type_info = type_store.get_type_info(v);
                    interner.resolve_lexeme(type_info.name)
                });
                write!(&mut message, "`{kind}`, ").unwrap();
            }

            let kind = analyzer.value_types([*last]).map_or("Unknown", |[v]| {
                let type_info = type_store.get_type_info(v);
                interner.resolve_lexeme(type_info.name)
            });
            write!(&mut message, "and `{kind}`").unwrap();
        }
    }

    let mut bad_values = Vec::new();
    for (value_id, order) in types.iter().rev().zip(1..) {
        let value_type = analyzer.value_types([*value_id]).map_or("Unknown", |[v]| {
            let type_info = type_store.get_type_info(v);
            interner.resolve_lexeme(type_info.name)
        });
        bad_values.push((*value_id, order, value_type));
    }

    let mut labels =
        diagnostics::build_creator_label_chain(analyzer, bad_values, Color::Yellow, Color::Cyan);
    labels.push(Label::new(op.token.location).with_color(Color::Red));
    diagnostics::emit_error(op.token.location, message, labels, None, source_store);
}

fn generate_stack_length_mismatch_diag(
    source_store: &SourceStorage,
    sample_location: SourceLocation,
    error_location: SourceLocation,
    actual: usize,
    expected: usize,
) {
    let message = format!("expected {expected} items, found {actual}");

    let labels = if sample_location != error_location {
        vec![
            Label::new(sample_location)
                .with_color(Color::Cyan)
                .with_message(format!("{expected} values here...",)),
            Label::new(error_location)
                .with_color(Color::Red)
                .with_message(format!("... but found {actual} values here")),
        ]
    } else {
        vec![Label::new(error_location)
            .with_color(Color::Red)
            .with_message("here")]
    };

    diagnostics::emit_error(sample_location, message, labels, None, source_store);
}

fn analyze_block(
    program: &Program,
    item_id: ItemId,
    block: &[Op],
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    had_error: &mut bool,
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    emit_traces: bool,
) {
    let mut op_iter = block.iter();

    for op in op_iter.by_ref() {
        match &op.code {
            OpCode::Add => {
                let mut local_had_error = false;
                eat_two_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::arithmetic::add(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::arithmetic::add(analyzer, type_store, op);
                }

                *had_error |= local_had_error;
            }
            OpCode::Div
            | OpCode::Multiply
            | OpCode::Rem
            | OpCode::ShiftLeft
            | OpCode::ShiftRight => {
                let mut local_had_error = false;
                eat_two_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::arithmetic::multiply_div_rem_shift(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::arithmetic::multiply_div_rem_shift(
                        analyzer,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::Subtract => {
                let mut local_had_error = false;
                eat_two_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::arithmetic::subtract(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::arithmetic::subtract(
                        analyzer,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }

            OpCode::BitAnd | OpCode::BitOr | OpCode::BitXor => {
                let mut local_had_error = false;
                eat_two_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::arithmetic::bitand_bitor_bitxor(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::arithmetic::bitand_bitor_bitxor(analyzer, type_store, op);
                }

                *had_error |= local_had_error;
            }
            OpCode::BitNot => {
                let mut local_had_error = false;
                eat_one_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::arithmetic::bitnot(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::arithmetic::bitnot(analyzer, type_store, op);
                }

                *had_error |= local_had_error;
            }

            OpCode::Equal | OpCode::NotEq => {
                let mut local_had_error = false;
                eat_two_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::comparative::equal(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::comparative::equal(
                        analyzer,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::IsNull => {
                let mut local_had_error = false;
                eat_one_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::comparative::is_null(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::comparative::is_null(analyzer, op);
                }
            }

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                let mut local_had_error = false;
                eat_two_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::comparative::compare(
                        analyzer,
                        source_store,
                        interner,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::comparative::compare(
                        analyzer,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }

            OpCode::Drop { count, count_token } => {
                stack_check::stack_ops::drop(
                    analyzer,
                    stack,
                    source_store,
                    had_error,
                    op,
                    *count,
                    *count_token,
                );
            }
            OpCode::Dup { count, count_token } => {
                let mut local_had_error = false;
                stack_check::stack_ops::dup(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *count,
                    *count_token,
                );
                if !local_had_error {
                    type_check2::stack_ops::dup(analyzer, op);
                    const_prop::stack_ops::dup(analyzer, op);
                }

                *had_error |= local_had_error;
            }
            OpCode::ExtractArray { emit_array } => {
                let mut local_had_error = false;
                stack_check::memory::extract_array(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *emit_array,
                );
                if !local_had_error {
                    type_check2::memory::extract_array(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *emit_array,
                    );
                }
                if !local_had_error {
                    const_prop::memory::extract_array(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::InsertArray { emit_array } => {
                let mut local_had_error = false;
                stack_check::memory::insert_array(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *emit_array,
                );
                if !local_had_error {
                    type_check2::memory::insert_array(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *emit_array,
                    );
                }
                if !local_had_error {
                    const_prop::memory::insert_array(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    )
                }

                *had_error |= local_had_error;
            }
            OpCode::ExtractStruct {
                emit_struct,
                field_name,
            } => {
                let mut local_had_error = false;
                stack_check::memory::extract_struct(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *emit_struct,
                );
                if !local_had_error {
                    type_check2::memory::extract_struct(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *field_name,
                        *emit_struct,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::InsertStruct {
                emit_struct,
                field_name,
            } => {
                let mut local_had_error = false;
                stack_check::memory::insert_struct(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *emit_struct,
                );
                if !local_had_error {
                    type_check2::memory::insert_struct(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *field_name,
                        *emit_struct,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::Over { depth, .. } => {
                let mut local_had_error = false;
                stack_check::stack_ops::over(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *depth,
                );
                if !local_had_error {
                    type_check2::stack_ops::over(analyzer, op);
                    const_prop::stack_ops::over(analyzer, op);
                }

                *had_error |= local_had_error;
            }
            OpCode::PackArray { count } => {
                let mut local_had_error = false;
                stack_check::memory::pack_array(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *count,
                );
                if !local_had_error {
                    type_check2::memory::pack_array(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *count,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::PackStruct { id } => {
                let mut local_had_error = false;
                stack_check::memory::pack_struct(
                    analyzer,
                    stack,
                    source_store,
                    type_store,
                    &mut local_had_error,
                    op,
                    *id,
                );
                if !local_had_error {
                    type_check2::memory::pack_struct(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *id,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::Reverse { count, count_token } => {
                stack_check::stack_ops::reverse(
                    analyzer,
                    stack,
                    source_store,
                    had_error,
                    op,
                    *count,
                    *count_token,
                );
            }
            OpCode::Rot {
                item_count,
                direction,
                shift_count,
                item_count_token,
                shift_count_token,
            } => {
                stack_check::stack_ops::rot(
                    analyzer,
                    stack,
                    source_store,
                    had_error,
                    op,
                    *item_count,
                    *direction,
                    *shift_count,
                    *item_count_token,
                    *shift_count_token,
                );
            }
            OpCode::Swap { count, count_token } => {
                stack_check::stack_ops::swap(
                    analyzer,
                    stack,
                    source_store,
                    had_error,
                    op,
                    *count,
                    *count_token,
                );
            }
            OpCode::Unpack => {
                let mut local_had_error = false;
                stack_check::memory::unpack(
                    analyzer,
                    stack,
                    interner,
                    source_store,
                    type_store,
                    &mut local_had_error,
                    op,
                );
                if !local_had_error {
                    type_check2::memory::unpack(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }

            OpCode::ArgC => {
                make_one(analyzer, stack, op);
                type_check2::stack_ops::push_int(
                    analyzer,
                    type_store,
                    op,
                    IntWidth::I64,
                    Signedness::Unsigned,
                );
            }
            OpCode::ArgV => {
                make_one(analyzer, stack, op);
                type_check2::stack_ops::push_str(analyzer, type_store, op, true);
            }
            OpCode::PushBool(v) => {
                make_one(analyzer, stack, op);
                type_check2::stack_ops::push_bool(analyzer, type_store, op);
                const_prop::stack_ops::push_bool(analyzer, op, *v);
            }
            OpCode::PushInt { width, value } => {
                make_one(analyzer, stack, op);
                type_check2::stack_ops::push_int(
                    analyzer,
                    type_store,
                    op,
                    *width,
                    value.to_signedness(),
                );
                const_prop::stack_ops::push_int(analyzer, op, *value);
            }
            OpCode::SizeOf(kind) => {
                make_one(analyzer, stack, op);
                let size_info = type_store.get_size_info(*kind);
                type_check2::stack_ops::push_int(
                    analyzer,
                    type_store,
                    op,
                    IntWidth::I64,
                    Signedness::Unsigned,
                );
                const_prop::stack_ops::push_int(
                    analyzer,
                    op,
                    IntKind::Unsigned(size_info.byte_width),
                );
            }
            OpCode::PushStr { id, is_c_str } => {
                stack_check::stack_ops::push_str(analyzer, stack, op);
                type_check2::stack_ops::push_str(analyzer, type_store, op, *is_c_str);
                const_prop::stack_ops::push_str(analyzer, op, *id, *is_c_str);
            }

            OpCode::Load => {
                let mut local_had_error = false;
                eat_one_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::memory::load(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }
                if !local_had_error {
                    const_prop::memory::load(
                        analyzer,
                        source_store,
                        interner,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }
            OpCode::Memory { .. } => todo!(),
            OpCode::Store => {
                let mut local_had_error = false;
                stack_check::memory::store(analyzer, stack, source_store, &mut local_had_error, op);
                if !local_had_error {
                    type_check2::memory::store(
                        program,
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }

            OpCode::CallFunction { .. } => todo!(),
            OpCode::Epilogue | OpCode::Return => {
                let mut local_had_error = false;
                stack_check::control::epilogue_return(
                    program,
                    analyzer,
                    stack,
                    source_store,
                    interner,
                    &mut local_had_error,
                    op,
                    item_id,
                );
                if !local_had_error {
                    type_check2::control::epilogue_return(
                        program,
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        item_id,
                    );
                }
                if !local_had_error {
                    const_prop::control::epilogue_return(
                        program,
                        analyzer,
                        source_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
                break;
            }
            OpCode::Exit => {
                analyzer.set_op_io(op, &[], &[]);
                break;
            }
            OpCode::Prologue => {
                let item_sig = program.get_item_signature_resolved(item_id);
                let item_tokens = program.get_item_signature_unresolved(item_id);
                stack_check::control::prologue(analyzer, stack, op, item_tokens);
                type_check2::control::prologue(analyzer, op, item_sig);
            }
            OpCode::SysCall {
                arg_count,
                arg_count_token,
            } => {
                let mut local_had_error = false;
                stack_check::control::syscall(
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *arg_count,
                    *arg_count_token,
                );
                if !local_had_error {
                    type_check2::control::syscall(
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                    );
                }

                *had_error |= local_had_error;
            }

            OpCode::If(if_op) => {
                let mut local_had_error = false;
                stack_check::control::analyze_if(
                    program,
                    item_id,
                    analyzer,
                    stack,
                    max_stack_depth,
                    &mut local_had_error,
                    interner,
                    source_store,
                    type_store,
                    op,
                    if_op,
                    emit_traces,
                );
                if !local_had_error {
                    type_check2::control::analyze_if(
                        &mut local_had_error,
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        op,
                        if_op,
                    );
                }

                *had_error |= local_had_error;

                if if_op.is_else_terminal && if_op.is_then_terminal {
                    // Clearly our block diverges if both branches do.
                    break;
                }
            }
            OpCode::While(while_op) => {
                let mut local_had_error = false;
                // This feels a bit hacky, but we need to inhibit the const-vals of previous values before
                // analyzing the while, but in order to find out which values to inhibit we need to analyze
                // the while...
                let mut initial_analyzer = analyzer.clone();

                stack_check::control::analyze_while(
                    program,
                    item_id,
                    analyzer,
                    stack,
                    max_stack_depth,
                    &mut local_had_error,
                    interner,
                    source_store,
                    type_store,
                    op,
                    while_op,
                    false,
                );

                let merges = analyzer.get_while_merges(op.id).unwrap();
                for merge in merges.condition.iter().chain(&merges.body) {
                    initial_analyzer.clear_value_const(merge.pre_value);
                }

                *analyzer = initial_analyzer;
                // Now we can run it again with the values properly inhibited.
                stack_check::control::analyze_while(
                    program,
                    item_id,
                    analyzer,
                    stack,
                    max_stack_depth,
                    &mut local_had_error,
                    interner,
                    source_store,
                    type_store,
                    op,
                    while_op,
                    emit_traces,
                );

                if !local_had_error {
                    type_check2::control::analyze_while(
                        &mut local_had_error,
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        op,
                        while_op,
                    );
                }

                *had_error |= local_had_error;
            }

            OpCode::ResolvedCast { id } => {
                let mut local_had_error = false;
                eat_one_make_one(analyzer, stack, source_store, &mut local_had_error, op);
                let type_info = type_store.get_type_info(*id);
                if !local_had_error {
                    match type_info.kind {
                        TypeKind::Integer { width, signed } => type_check2::stack_ops::cast_to_int(
                            analyzer,
                            source_store,
                            interner,
                            type_store,
                            &mut local_had_error,
                            op,
                            width,
                            signed,
                        ),
                        TypeKind::Pointer(kind) => type_check2::stack_ops::cast_to_ptr(
                            analyzer,
                            source_store,
                            interner,
                            type_store,
                            &mut local_had_error,
                            op,
                            kind,
                        ),
                        TypeKind::Bool
                        | TypeKind::Array { .. }
                        | TypeKind::Struct(_)
                        | TypeKind::StructInstance(_) => {
                            diagnostics::emit_error(
                                op.token.location,
                                format!(
                                    "cannot cast to {}",
                                    interner.resolve_lexeme(type_info.name)
                                ),
                                [Label::new(op.token.location).with_color(Color::Red)],
                                None,
                                source_store,
                            );
                            local_had_error = true;
                        }
                    }
                }

                if !local_had_error {
                    match type_info.kind {
                        TypeKind::Integer { width, signed } => {
                            const_prop::stack_ops::cast_to_int(analyzer, op, width, signed)
                        }
                        TypeKind::Pointer(kind) => {
                            const_prop::stack_ops::cast_to_ptr(analyzer, op, kind)
                        }
                        TypeKind::Bool
                        | TypeKind::Array { .. }
                        | TypeKind::Struct(_)
                        | TypeKind::StructInstance(_) => {}
                    }
                }

                *had_error |= local_had_error;
            }
            OpCode::ResolvedIdent {
                item_id: resolved_item,
            } => {
                let mut local_had_error = false;
                stack_check::control::resolved_ident(
                    program,
                    analyzer,
                    stack,
                    source_store,
                    &mut local_had_error,
                    op,
                    *resolved_item,
                );
                if !local_had_error {
                    type_check2::control::resolved_ident(
                        program,
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        &mut local_had_error,
                        op,
                        *resolved_item,
                    );
                }
                if !local_had_error {
                    const_prop::control::resolved_ident(program, analyzer, op, *resolved_item);
                }

                *had_error |= local_had_error;
            }

            OpCode::EmitStack(emit_labels) => {
                if emit_traces {
                    type_check2::stack_ops::emit_stack(
                        stack,
                        analyzer,
                        interner,
                        source_store,
                        type_store,
                        op,
                        *emit_labels,
                    );
                }
            }

            OpCode::UnresolvedCast { .. }
            | OpCode::UnresolvedIdent(_)
            | OpCode::UnresolvedPackStruct { .. }
            | OpCode::UnresolvedSizeOf { .. } => {
                panic!("ICE: Encountered {:?}", op.code);
            }
        }

        *max_stack_depth = std::cmp::max(*max_stack_depth, stack.len());
    }

    for op in op_iter {
        if matches!(&op.code, OpCode::Epilogue) {
            // Implicitly added to procs, we don't want to diagnose these.
            continue;
        }
        diagnostics::emit_warning(
            op.token.location,
            "unreachable op",
            [Label::new(op.token.location).with_color(Color::Yellow)],
            None,
            source_store,
        );
    }
}

pub fn analyze_item(
    program: &Program,
    item_id: ItemId,
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    print_stack_depth: bool,
) -> Result<(), ()> {
    let mut stack = Vec::new();
    let mut had_error = false;
    let mut max_stack_depth = 0;

    analyze_block(
        program,
        item_id,
        program.get_item_body(item_id),
        &mut stack,
        &mut max_stack_depth,
        &mut had_error,
        analyzer,
        interner,
        source_store,
        type_store,
        true,
    );

    if print_stack_depth {
        let item_name = interner.get_symbol_name(program, item_id);
        println!("{item_name}: {max_stack_depth}");
    }

    had_error.not().then_some(()).ok_or(())
}
