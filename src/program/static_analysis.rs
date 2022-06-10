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

mod const_prop;
mod data_flow;
mod type_check2;

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
pub struct Analyzer {
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

fn check_allowed_const<const N: usize>(
    inputs: Option<[ValueId; N]>,
    before: Option<ValueId>,
) -> bool {
    match (inputs, before) {
        // If the inputs are None, it means a stack exhaustion, so there can be no consts to begin with,
        // if before is None then there's no limit to const values.
        (Some(vals), Some(before_id)) => vals.iter().all(|&v| v > before_id),
        _ => true,
    }
}

pub fn data_flow_analysis(
    program: &Program,
    proc: &Procedure,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<Analyzer, ()> {
    let mut analyzer = Analyzer::default();
    let mut stack = Vec::new();
    let mut had_error = false;

    data_flow::analyze_block(
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

    had_error.not().then(|| analyzer).ok_or(())
}

pub fn type_check(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;

    type_check2::analyze_block(
        program,
        proc,
        proc.body(),
        analyzer,
        &mut had_error,
        interner,
        source_store,
    );

    had_error.not().then(|| ()).ok_or(())
}

pub fn const_propagation(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;

    const_prop::analyze_block(
        program,
        proc,
        proc.body(),
        analyzer,
        &mut had_error,
        interner,
        source_store,
    );

    had_error.not().then(|| ()).ok_or(())
}
