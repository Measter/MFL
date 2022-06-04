use std::{collections::HashMap, fmt::Write, ops::Not};

use ariadne::{Color, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    opcode::{Op, OpCode},
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct ValueId(usize);

#[derive(Debug)]
struct Value {
    value_id: ValueId,
    creator_op_idx: usize,
    creator_token: Token,
    porth_type: PorthTypeKind,
    const_val: Option<ConstVal>,
    consumer: Vec<usize>,
}

#[derive(Debug)]
struct OpData {
    op: Token,
    idx: usize,
    inputs: Vec<ValueId>,
    outputs: Vec<ValueId>,
}

#[derive(Debug, Default)]
struct Analyzer {
    values: HashMap<ValueId, Value>,
    current_id: usize,
    ios: HashMap<usize, OpData>,
}

impl Analyzer {
    fn new_value(
        &mut self,
        porth_type: PorthTypeKind,
        creator_idx: usize,
        creator_token: Token,
    ) -> (ValueId, &mut Value) {
        let id = ValueId(self.current_id);
        self.current_id += 1;
        (
            id,
            self.values.entry(id).or_insert(Value {
                value_id: id,
                creator_op_idx: creator_idx,
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

    fn consume(&mut self, value: ValueId, consumer_id: usize) {
        let val = self.values.get_mut(&value).unwrap();
        val.consumer.push(consumer_id);
    }

    fn set_io(&mut self, op_idx: usize, op: Token, inputs: &[ValueId], outputs: &[ValueId]) {
        let prev = self.ios.insert(
            op_idx,
            OpData {
                op,
                idx: op_idx,
                inputs: inputs.to_owned(),
                outputs: outputs.to_owned(),
            },
        );

        assert!(prev.is_none(), "Set operands twice");
    }
}

fn failed_compare_stack_types(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    actual_stack: &[ValueId],
    expected_stack: &[PorthType],
    cur_op: &Op,
    open_token: Token,
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
            expected.kind,
            actual_value.porth_type
        )
        .unwrap();
    }

    diagnostics::emit_error(
        open_token.location,
        msg,
        [
            Label::new(cur_op.token.location)
                .with_color(Color::Red)
                .with_message("actual sampled here"),
            Label::new(open_token.location)
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

    let mut labels = vec![Label::new(op.token.location)
        .with_color(Color::Red)
        .with_message(" ")];

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

fn generate_stack_exhaustion_diag(
    source_store: &SourceStorage,
    op: &Op,
    actual: usize,
    expected: usize,
) {
    let message = format!("expected {} items, found {}", expected, actual);

    let mut labels = vec![Label::new(op.token.location)
        .with_color(Color::Red)
        .with_message("here")];

    for source in op.expansions.iter() {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    diagnostics::emit_error(op.token.location, message, labels, None, source_store);
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

    for (op_idx, op) in proc.body().iter().enumerate() {
        match op.code {
            OpCode::Add => arithmetic::add(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
            ),
            OpCode::Subtract => arithmetic::subtract(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
            ),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => {
                arithmetic::multiply_and_shift(
                    &mut analyzer,
                    &mut stack,
                    source_store,
                    interner,
                    &mut had_error,
                    op_idx,
                    op,
                )
            }
            OpCode::DivMod => arithmetic::divmod(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                comparative::compare(
                    &mut analyzer,
                    &mut stack,
                    source_store,
                    interner,
                    &mut had_error,
                    op_idx,
                    op,
                )
            }
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(&mut analyzer, &mut stack, op_idx, op, v),
            OpCode::PushInt(v) => stack_ops::push_int(&mut analyzer, &mut stack, op_idx, op, v),
            OpCode::PushStr { is_c_str, id } => stack_ops::push_str(
                &mut analyzer,
                &mut stack,
                interner,
                op_idx,
                op,
                is_c_str,
                id,
            ),
            OpCode::ArgC => stack_ops::push_argc(
                &mut analyzer,
                &mut stack,
                op_idx,
                op
            ),
            
            OpCode::ArgV => stack_ops::push_argv(
                &mut analyzer,
                &mut stack,
                op_idx,
                op
            ),

            OpCode::CastInt => stack_ops::cast_int(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op
            ),
            OpCode::CastPtr => stack_ops::cast_ptr(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op
            ),  

            OpCode::While { .. } => unimplemented!(),

            OpCode::If => unimplemented!(),
            OpCode::DoIf { .. } => unimplemented!(),
            OpCode::Elif { .. } | OpCode::Else { .. } => unimplemented!(),
            OpCode::EndIf { .. } => unimplemented!(),

            OpCode::Drop => stack_ops::drop(
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
            ),
            OpCode::Dup { depth } => stack_ops::dup(
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
                depth,
            ),
            OpCode::DupPair => stack_ops::dup_pair(
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
            ),
            OpCode::Swap => stack_ops::swap(
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
            ),
            OpCode::Rot => stack_ops::rot(
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
            ),

            OpCode::Load { width, kind } => memory::load(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
                width,
                kind,
            ),
            OpCode::Store { kind, .. } => memory::store(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
                kind,
            ),

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
                proc_id,
            ),
            OpCode::SysCall(num_args @ 0..=6) => control::syscall(
                &mut analyzer,
                &mut stack,
                source_store,
                &mut had_error,
                op_idx,
                op,
                num_args,
            ),

            OpCode::Prologue => control::prologue(&mut analyzer, &mut stack, op_idx, op, proc),
            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                &mut analyzer,
                &mut stack,
                source_store,
                interner,
                &mut had_error,
                op_idx,
                op,
                proc,
            ),

            // TODO: Remove this opcode.
            OpCode::CastBool => panic!("Unsupported"),

            OpCode::SysCall(_) // No syscalls with this many args.
            | OpCode::CallProc { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            | OpCode::End // All of these should be specialized.
            | OpCode::Do // As should these.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }

    // dbg!(analyzer);

    had_error.not().then(|| ()).ok_or(())
}
