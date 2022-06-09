#![allow(unused)]

use std::{collections::HashMap, fmt::Write, ops::Not};

use ariadne::{Color, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    opcode::{Op, OpCode, OpId},
    program::{Procedure, ProcedureId, Program},
    source_file::{SourceLocation, SourceStorage},
    type_check::{PorthType, PorthTypeKind},
};

#[macro_export]
macro_rules! type_pattern {
    ($( $const_name:tt @ $p:pat_param ),+) => {
        [
            $( Value { porth_type: $p, const_val: $const_name, .. } ),+
        ]
    };
}

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum PtrId {
    Mem(ProcedureId),
    Str(Spur),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum ConstVal {
    Int(u64),
    Bool(bool),
    Ptr {
        id: PtrId,
        src_op_loc: SourceLocation,
        offset: Option<u64>,
    },
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct ValueId(usize);

#[derive(Debug)]
struct Value {
    value_id: ValueId,
    creator_id: OpId,
    creator_token: Token,
    porth_type: PorthTypeKind,
    const_val: Option<ConstVal>,
    consumer: Vec<OpId>,
}

#[derive(Debug)]
struct OpData {
    op: Token,
    idx: OpId,
    inputs: Vec<ValueId>,
    outputs: Vec<ValueId>,
}

#[derive(Debug, Default)]
struct Analyzer {
    values: HashMap<ValueId, Value>,
    next_value_id: usize,
    ios: HashMap<OpId, OpData>,
}

impl Analyzer {
    fn new_value(
        &mut self,
        porth_type: PorthTypeKind,
        creator_id: OpId,
        creator_token: Token,
    ) -> (ValueId, &mut Value) {
        let id = ValueId(self.next_value_id);
        self.next_value_id += 1;
        (
            id,
            self.values.entry(id).or_insert(Value {
                value_id: id,
                creator_id,
                creator_token,
                porth_type,
                const_val: None,
                consumer: Vec::new(),
            }),
        )
    }

    fn get_values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.values[&id])
    }

    fn value_mut(&mut self, id: ValueId) -> &mut Value {
        self.values.get_mut(&id).unwrap()
    }

    fn consume(&mut self, value: ValueId, consumer_id: OpId) {
        let val = self.values.get_mut(&value).unwrap();
        val.consumer.push(consumer_id);
    }

    fn set_io(&mut self, op_idx: OpId, op: Token, inputs: &[ValueId], outputs: &[ValueId]) {
        let prev = self.ios.insert(
            op_idx,
            OpData {
                op,
                idx: op_idx,
                inputs: inputs.to_owned(),
                outputs: outputs.to_owned(),
            },
        );

        assert!(
            prev.is_none(),
            "Set operands twice - cur_token: {:#?}, prev_token: {:#?}",
            op,
            prev
        );
    }

    fn last_value_id(&self) -> Option<ValueId> {
        self.next_value_id.checked_sub(1).map(ValueId)
    }
}

fn failed_compare_stack_types(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    actual_stack: &[ValueId],
    expected_stack: &[PorthTypeKind],
    sample_location: SourceLocation,
    error_location: SourceLocation,
    msg: &str,
) {
    let mut note = "\n\t\tDepth | Expected |   Actual\n\
        \t\t______|__________|_________"
        .to_owned();

    let pairs = expected_stack.iter().zip(actual_stack).enumerate().rev();
    for (idx, (expected, actual_id)) in pairs {
        let [actual_value] = analyzer.get_values([*actual_id]);
        write!(
            &mut note,
            "\n\t\t{:<5} | {:<8} | {:>8}",
            actual_stack.len() - idx - 1,
            expected,
            actual_value.porth_type
        )
        .unwrap();
    }

    diagnostics::emit_error(
        error_location,
        msg,
        [
            Label::new(error_location)
                .with_color(Color::Red)
                .with_message("actual sampled here"),
            Label::new(sample_location)
                .with_color(Color::Cyan)
                .with_message("expected sampled here"),
        ],
        note,
        source_store,
    );
}

fn generate_type_mismatch_diag(
    source_store: &SourceStorage,
    operator_str: &str,
    op: &Op,
    types: &[&Value],
) {
    let mut message = format!("cannot use `{}` on ", operator_str);
    match types {
        [] => unreachable!(),
        [a] => write!(&mut message, "`{}`", a.porth_type).unwrap(),
        [a, b] => write!(&mut message, "`{}` and `{}`", a.porth_type, b.porth_type).unwrap(),
        [xs @ .., last] => {
            for x in xs {
                write!(&mut message, "`{}`, ", x.porth_type).unwrap();
            }

            write!(&mut message, "and `{}`", last.porth_type).unwrap();
        }
    }

    let mut labels = vec![Label::new(op.token.location).with_color(Color::Red)];

    for source in op.expansions.iter() {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    for (value, order) in types.iter().rev().zip(1..) {
        labels.push(
            Label::new(value.creator_token.location)
                .with_color(Color::Yellow)
                .with_message(format!("{}", value.porth_type))
                .with_order(order),
        )
    }

    diagnostics::emit_error(op.token.location, message, labels, None, source_store);
}

fn generate_stack_length_mismatch_diag(
    source_store: &SourceStorage,
    op: &Op,
    sample_location: SourceLocation,
    actual: usize,
    expected: usize,
) {
    let message = format!("expected {} items, found {}", expected, actual);

    let mut labels = vec![Label::new(sample_location)
        .with_color(Color::Red)
        .with_message("here")];

    for source in op.expansions.iter() {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    diagnostics::emit_error(sample_location, message, labels, None, source_store);
}

fn check_allowed_const<const N: usize>(inputs: Option<[ValueId; N]>, before: Option<ValueId>) -> bool {
    match (inputs, before) {
        // If the inputs are None, it means a stack exhaustion, so there can be no consts to begin with,
        // if before is None then there's no limit to const values.
        (Some(vals), Some(before_id)) => vals.iter().all(|&v| v > before_id),
        _ => true
    }
}

fn analyze_block(
    program: &Program,
    proc: &Procedure,
    block: &[Op],
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    force_non_const_before: Option<ValueId>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in block {
        match op.code {
            OpCode::Add => arithmetic::add(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => {
                arithmetic::multiply_and_shift(
                    analyzer,
                    stack,
                    source_store,
                    interner,
                    had_error,
                force_non_const_before,
                    op,
                )
            }
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                comparative::compare(
                    analyzer,
                    stack,
                    source_store,
                    interner,
                    had_error,
                    force_non_const_before,
                    op,
                )
            }
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(
                analyzer,
                stack,
                op,
                v
            ),
            OpCode::PushInt(v) => stack_ops::push_int(
                analyzer,
                stack,
                op,v
            ),
            OpCode::PushStr { is_c_str, id } => stack_ops::push_str(
                analyzer,
                stack,
                interner,
                op,
                is_c_str,
                id,
            ),

            OpCode::ArgC => stack_ops::push_argc(
                analyzer,
                stack,
                op
            ),
            OpCode::ArgV => stack_ops::push_argv(
                analyzer,
                stack,
                op
            ),

            OpCode::CastInt => stack_ops::cast_int(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op
            ),
            OpCode::CastPtr => stack_ops::cast_ptr(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op
            ),  

            OpCode::While { ref body  } => {
                control::analyze_while(
                    program,
                    proc,
                    analyzer,
                    stack,
                    had_error,
                    interner,
                    source_store,
                    op,
                    body,
                )
            },
            OpCode::If {..} => unimplemented!(),

            OpCode::Drop => stack_ops::drop(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),
            OpCode::Dup { depth } => stack_ops::dup(
                analyzer,
                stack,
                source_store,
                had_error,
                force_non_const_before,
                op,
                depth,
            ),
            OpCode::DupPair => stack_ops::dup_pair(
                analyzer,
                stack,
                source_store,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Swap => stack_ops::swap(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),
            OpCode::Rot => stack_ops::rot(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),

            OpCode::Load { width, kind } => memory::load(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                width,
                kind,
            ),
            OpCode::Store { kind, .. } => memory::store(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                kind,
            ),

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                proc_id,
            ),
            OpCode::SysCall(num_args @ 0..=6) => control::syscall(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                num_args,
            ),

            OpCode::Prologue => control::prologue(analyzer,  stack,  op, proc),
            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                proc,
            ),

            // TODO: Remove this opcode.
            OpCode::CastBool => panic!("Unsupported"),

            OpCode::SysCall(_) // No syscalls with this many args.
            | OpCode::CallProc { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}

pub fn analyze(
    program: &Program,
    proc: &Procedure,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut analyzer = Analyzer::default();
    let mut stack = Vec::new();
    let mut had_error = false;

    analyze_block(
        program,
        proc,
        proc.body(),
        &mut analyzer,
        &mut stack,
        None,
        &mut had_error,
        interner,
        source_store,
    );

    // dbg!(analyzer);

    had_error.not().then(|| ()).ok_or(())
}
