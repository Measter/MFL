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
    type_check::PorthTypeKind,
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
        source_op_location: SourceLocation,
        offset: u64,
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
    consumer: Option<usize>,
}

#[derive(Debug, Default)]
struct Analyzer {
    values: HashMap<ValueId, Value>,
    current_id: usize,
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
                consumer: None,
            }),
        )
    }

    fn get_values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.values[&id])
    }

    fn value_mut(&mut self, id: ValueId) -> &mut Value {
        self.values.get_mut(&id).unwrap()
    }
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
                &mut stack,
                &mut analyzer,
                op_idx,
                source_store,
                op,
                &mut had_error,
                interner,
            ),
            OpCode::Subtract => arithmetic::subtract(
                &mut stack,
                &mut analyzer,
                op_idx,
                source_store,
                op,
                &mut had_error,
                interner,
            ),

            OpCode::Equal | OpCode::NotEq => comparative::equal(
                &mut stack,
                &mut analyzer,
                op_idx,
                source_store,
                op,
                &mut had_error,
                interner,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(&mut analyzer, op_idx, op, v, &mut stack),
            OpCode::PushInt(v) => stack_ops::push_int(&mut analyzer, op_idx, op, v, &mut stack),
            OpCode::PushStr { is_c_str, id } => stack_ops::push_str(
                is_c_str,
                &mut analyzer,
                op_idx,
                op,
                interner,
                id,
                &mut stack,
            ),

            OpCode::Drop => stack_ops::drop(
                &mut stack,
                source_store,
                op,
                &mut had_error,
                &mut analyzer,
                op_idx,
            ),
            OpCode::Dup { depth } => stack_ops::dup(
                &mut stack,
                &mut analyzer,
                op_idx,
                source_store,
                op,
                &mut had_error,
                depth,
            ),
            OpCode::DupPair => stack_ops::dup_pair(
                &mut stack,
                &mut analyzer,
                op_idx,
                source_store,
                op,
                &mut had_error,
            ),
            OpCode::Swap => stack_ops::swap(
                &mut stack,
                &mut analyzer,
                op_idx,
                source_store,
                op,
                &mut had_error,
            ),

            OpCode::Load { width, kind } => memory::load(
                &mut stack,
                source_store,
                op,
                &mut had_error,
                &mut analyzer,
                op_idx,
                interner,
                width,
                kind,
            ),

            OpCode::Prologue | OpCode::Epilogue => {
                // TODO: These should do some handling
            }
            OpCode::Return => {
                // TODO: Final stack check here.
            }
            _ => unimplemented!("{:?}", op.code),
        }
    }

    // dbg!(analyzer);

    had_error.not().then(|| ()).ok_or(())
}
