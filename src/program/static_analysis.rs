use std::{
    fmt::{self, Write},
    ops::Not,
};

use ariadne::{Color, Label};
use hashbrown::HashMap;
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::HashMapNOps,
    opcode::{Op, OpId},
    option::OptionExt,
    program::{Procedure, ProcedureId, Program},
    source_file::{SourceLocation, SourceStorage},
};

mod const_prop;
mod data_flow;
mod type_check2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PorthTypeKind {
    Int,
    Ptr,
    Bool,
}

impl PorthTypeKind {
    fn name_str(self) -> &'static str {
        match self {
            PorthTypeKind::Int => "Int",
            PorthTypeKind::Ptr => "Ptr",
            PorthTypeKind::Bool => "Bool",
        }
    }
}

#[derive(Debug, Clone, Copy, Eq)]
pub struct PorthType {
    pub kind: PorthTypeKind,
    // TODO: Replace this with source token.
    pub location: SourceLocation,
}

impl PartialEq for PorthType {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl fmt::Display for PorthTypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name_str())
    }
}

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
pub struct ValueId(usize);

#[derive(Debug)]
struct Value {
    value_id: ValueId,
    creator_token: Token,
    consumer: Vec<OpId>,
}

#[derive(Debug)]
pub struct OpData {
    inputs: Vec<ValueId>,
    outputs: Vec<ValueId>,
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
struct MergePair {
    src: ValueId,
    dst: ValueId,
}

#[derive(Debug)]
struct MergeBlock {
    condition_merges: Vec<MergePair>,
    body_merges: Vec<MergePair>,
}

#[derive(Debug, Default)]
pub struct Analyzer {
    value_lifetime: HashMap<ValueId, Value>,
    value_types: HashMap<ValueId, PorthTypeKind>,
    value_consts: HashMap<ValueId, ConstVal>,
    value_merges: HashMap<OpId, MergeBlock>,

    next_value_id: usize,
    ios: HashMap<OpId, OpData>,
}

impl Analyzer {
    fn new_value(&mut self, creator: &Op) -> ValueId {
        let id = ValueId(self.next_value_id);
        self.next_value_id += 1;

        let value_exists = self
            .value_lifetime
            .insert(
                id,
                Value {
                    value_id: id,
                    creator_token: creator.token,
                    consumer: Vec::new(),
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

    fn value_types<const N: usize>(&self, ids: [ValueId; N]) -> Option<[PorthTypeKind; N]> {
        self.value_types.get_n(ids)
    }

    fn set_value_type(&mut self, id: ValueId, kind: PorthTypeKind) {
        self.value_types
            .insert(id, kind)
            .expect_none("ICE: Tried to set a value type twice");
    }

    pub fn value_consts<const N: usize>(&self, ids: [ValueId; N]) -> Option<[ConstVal; N]> {
        self.value_consts.get_n(ids)
    }

    fn set_value_const(&mut self, id: ValueId, const_val: ConstVal) {
        self.value_consts
            .insert(id, const_val)
            .expect_none("ICE: Tried to overwrite const value");
    }

    fn clear_value_const(&mut self, id: ValueId) {
        self.value_consts.remove(&id);
    }

    fn set_op_merges(&mut self, op: &Op, merges: MergeBlock) {
        self.value_merges
            .insert(op.id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    fn get_op_merges(&self, op_id: OpId) -> Option<&MergeBlock> {
        self.value_merges.get(&op_id)
    }

    fn set_op_io(&mut self, op: &Op, inputs: &[ValueId], outputs: &[ValueId]) {
        let prev = self.ios.insert(
            op.id,
            OpData {
                inputs: inputs.to_owned(),
                outputs: outputs.to_owned(),
            },
        );

        assert!(
            prev.is_none(),
            "Set operands twice - cur_token: {op:#?}, prev_token: {prev:#?}"
        );
    }

    pub fn get_op_io(&self, op_idx: OpId) -> &OpData {
        &self.ios[&op_idx]
    }
}

fn failed_compare_stack_types(
    analyzer: &Analyzer,
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
        let value_type = analyzer
            .value_types([*actual_id])
            .map_or("Unknown", |[v]| v.name_str());

        write!(
            &mut note,
            "\n\t\t{:<5} | {:<8} | {:>8}",
            actual_stack.len() - idx - 1,
            expected.name_str(),
            value_type,
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
    analyzer: &Analyzer,
    source_store: &SourceStorage,
    operator_str: &str,
    op: &Op,
    types: &[ValueId],
) {
    let mut message = format!("cannot use `{operator_str}` on ");
    match types {
        [] => unreachable!(),
        [a] => {
            let kind = analyzer
                .value_types([*a])
                .map_or("Unknown", |[v]| v.name_str());
            write!(&mut message, "`{kind}`").unwrap();
        }
        [a, b] => {
            let [a, b] = analyzer
                .value_types([*a, *b])
                .map_or(["Unknown", "Unknown"], |k| k.map(PorthTypeKind::name_str));
            write!(&mut message, "`{a}` and `{b}`").unwrap()
        }
        [xs @ .., last] => {
            for x in xs {
                let kind = analyzer
                    .value_types([*x])
                    .map_or("Unknown", |[v]| v.name_str());
                write!(&mut message, "`{kind}`, ").unwrap();
            }

            let kind = analyzer
                .value_types([*last])
                .map_or("Unknown", |[v]| v.name_str());
            write!(&mut message, "and `{kind}`").unwrap();
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

    for (value_id, order) in types.iter().rev().zip(1..) {
        let [value] = analyzer.values([*value_id]);
        let value_type = analyzer
            .value_types([*value_id])
            .map_or("Unknown", |[v]| v.name_str());
        labels.push(
            Label::new(value.creator_token.location)
                .with_color(Color::Yellow)
                .with_message(value_type.to_string())
                .with_order(order),
        )
    }

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

pub fn data_flow_analysis(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut stack = Vec::new();
    let mut had_error = false;

    data_flow::analyze_block(
        program,
        proc,
        proc.body(),
        analyzer,
        &mut stack,
        &mut had_error,
        interner,
        source_store,
    );

    // dbg!(&analyzer);
    Ok(())
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

    had_error.not().then_some(()).ok_or(())
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

    // dbg!(&analyzer);

    had_error.not().then_some(()).ok_or(())
}
