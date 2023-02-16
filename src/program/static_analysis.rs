use std::{fmt::Write, ops::Not};

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::HashMapNOps,
    opcode::{Op, OpId},
    option::OptionExt,
    program::{ProcedureId, Program},
    source_file::{SourceLocation, SourceStorage},
};

use super::type_store::{IntWidth, TypeId, TypeStore};

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
pub struct ValueId(u16);

#[derive(Debug)]
struct Value {
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
    pub condition: Vec<WhileMerge>,
    pub body: Vec<WhileMerge>,
}

#[derive(Debug, Default)]
pub struct Analyzer {
    value_lifetime: HashMap<ValueId, Value>,
    value_types: HashMap<ValueId, TypeId>,
    value_consts: HashMap<ValueId, ConstVal>,

    op_if_merges: HashMap<OpId, Vec<IfMerge>>,
    op_while_merges: HashMap<OpId, WhileMerges>,

    op_io_data: HashMap<OpId, OpData>,
}

impl Analyzer {
    fn new_value(&mut self, creator: &Op) -> ValueId {
        let id = self.value_lifetime.len();
        let id = ValueId(id.to_u16().unwrap());

        let value_exists = self
            .value_lifetime
            .insert(
                id,
                Value {
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

    fn set_op_io(&mut self, op: &Op, inputs: &[ValueId], outputs: &[ValueId]) {
        let prev = self.op_io_data.insert(
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
        &self.op_io_data[&op_idx]
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
    for (idx, (expected, actual_id)) in pairs {
        let value_type = analyzer.value_types([*actual_id]).map_or("Unknown", |[v]| {
            let type_info = type_store.get_type_info(v);
            interner.resolve_lexeme(type_info.name)
        });

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
        let value_type = analyzer.value_types([*value_id]).map_or("Unknown", |[v]| {
            let type_info = type_store.get_type_info(v);
            interner.resolve_lexeme(type_info.name)
        });
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
    proc_id: ProcedureId,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut stack = Vec::new();
    let mut had_error = false;

    // TODO: Only pass in the proc id.
    data_flow::analyze_block(
        program,
        proc_id,
        program.get_proc_body(proc_id),
        analyzer,
        &mut stack,
        &mut had_error,
        interner,
        source_store,
    );

    // dbg!(&analyzer);
    had_error.not().then_some(()).ok_or(())
}

pub fn type_check(
    program: &Program,
    proc_id: ProcedureId,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;

    type_check2::analyze_block(
        program,
        proc_id,
        program.get_proc_body(proc_id),
        analyzer,
        &mut had_error,
        interner,
        source_store,
    );

    had_error.not().then_some(()).ok_or(())
}

pub fn const_propagation(
    program: &Program,
    proc_id: ProcedureId,
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;

    const_prop::analyze_block(
        program,
        proc_id,
        program.get_proc_body(proc_id),
        analyzer,
        &mut had_error,
        interner,
        source_store,
    );

    // dbg!(&analyzer);

    had_error.not().then_some(()).ok_or(())
}
