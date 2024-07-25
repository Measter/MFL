use std::fmt::{Display, Write};

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use prettytable::{row, Table};
use smallvec::SmallVec;

use crate::{
    context::ItemId,
    diagnostics::{self, TABLE_FORMAT},
    ir::IntKind,
    n_ops::HashMapNOps,
    option::OptionExt,
    stores::{
        ops::OpId,
        source::SourceLocation,
        types::{Integer, Signedness, TypeId},
    },
    Stores,
};

pub fn can_promote_int_unidirectional(from: Integer, to: Integer) -> bool {
    promote_int_type_uni_directional(from, to).is_some()
}

pub fn promote_int_type_uni_directional(from: Integer, to: Integer) -> Option<Integer> {
    if from.signed == Signedness::Unsigned
        && to.signed == Signedness::Signed
        && to.width > from.width
    {
        Some((to.width, Signedness::Signed).into())
    } else if from.signed == to.signed && to.width >= from.width {
        Some((to.width, to.signed).into())
    } else {
        None
    }
}

pub fn can_promote_int_bidirectional(a: Integer, b: Integer) -> bool {
    promote_int_type_bidirectional(a, b).is_some()
}

pub fn promote_int_type_bidirectional(a: Integer, b: Integer) -> Option<Integer> {
    promote_int_type_uni_directional(a, b).or_else(|| promote_int_type_uni_directional(b, a))
}

#[test]
fn test_promote_int() {
    use crate::stores::types::IntWidth::*;
    use Signedness::*;

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I16, Unsigned).into()),
        Some((I16, Unsigned,).into())
    );

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I32, Unsigned).into()),
        Some((I32, Unsigned).into())
    );

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I32, Signed).into()),
        Some((I32, Signed).into())
    );

    assert_eq!(
        promote_int_type_bidirectional((I16, Unsigned).into(), (I16, Signed).into()),
        None
    );
    assert_eq!(
        promote_int_type_bidirectional((I16, Signed).into(), (I64, Unsigned).into()),
        None
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtrId {
    Mem(ItemId),
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
pub(super) struct Value {
    pub(super) source_location: SourceLocation,
    pub(super) parent_value: Option<ValueId>,
    pub(super) consumer: SmallVec<[OpId; 4]>,
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
}

impl Analyzer {
    pub(super) fn new_value(
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

    pub fn value_count(&self) -> usize {
        self.value_lifetime.len()
    }

    pub(super) fn values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.value_lifetime[&id])
    }

    pub(super) fn consume_value(&mut self, value: ValueId, consumer_id: OpId) {
        let val = self.value_lifetime.get_mut(&value).unwrap();
        val.consumer.push(consumer_id);
    }

    pub fn value_types<const N: usize>(&self, ids: [ValueId; N]) -> Option<[TypeId; N]> {
        self.value_types.get_n(ids)
    }

    pub(super) fn set_value_type(&mut self, id: ValueId, kind: TypeId) {
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

    pub(super) fn clear_value_const(&mut self, id: ValueId) {
        self.value_consts.remove(&id);
    }

    pub(super) fn set_if_merges(&mut self, op_id: OpId, merges: Vec<IfMerge>) {
        self.op_if_merges
            .insert(op_id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    pub(super) fn set_while_merges(&mut self, op_id: OpId, merges: WhileMerges) {
        self.op_while_merges
            .insert(op_id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    pub fn get_if_merges(&self, op_id: OpId) -> Option<&Vec<IfMerge>> {
        self.op_if_merges.get(&op_id)
    }

    pub fn get_while_merges(&self, op_id: OpId) -> Option<&WhileMerges> {
        self.op_while_merges.get(&op_id)
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

pub(super) fn failed_compare_stack_types(
    stores: &Stores,
    analyzer: &Analyzer,
    actual_stack: &[ValueId],
    expected_stack: &[TypeId],
    sample_location: SourceLocation,
    error_location: SourceLocation,
    msg: &str,
) {
    let mut note = Table::new();
    note.set_format(*TABLE_FORMAT);
    note.set_titles(row!("Depth", "Expected", "Actual"));

    let pairs = expected_stack.iter().zip(actual_stack).enumerate().rev();
    let mut bad_values = Vec::new();
    for (idx, (expected, actual_id)) in pairs {
        let value_type = analyzer.value_types([*actual_id]).map_or("Unknown", |[v]| {
            let type_info = stores.types.get_type_info(v);
            stores.strings.resolve(type_info.name)
        });

        bad_values.push((*actual_id, idx.to_u64(), value_type));

        let expected_type_info = stores.types.get_type_info(*expected);
        let expected_name = stores.strings.resolve(expected_type_info.name);
        note.add_row(row!(
            (actual_stack.len() - idx - 1).to_string(),
            expected_name,
            value_type
        ));
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

    diagnostics::emit_error(stores, error_location, msg, labels, note.to_string());
}

pub(super) fn generate_type_mismatch_diag(
    stores: &Stores,
    analyzer: &Analyzer,
    operator_str: &str,
    op_id: OpId,
    types: &[ValueId],
) {
    let mut message = format!("cannot use `{operator_str}` on ");
    match types {
        [] => unreachable!(),
        [a] => {
            let kind = analyzer.value_types([*a]).map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.name)
            });
            write!(&mut message, "`{kind}`").unwrap();
        }
        [a, b] => {
            let [a, b] = analyzer
                .value_types([*a, *b])
                .map_or(["Unknown", "Unknown"], |k| {
                    k.map(|id| {
                        let type_info = stores.types.get_type_info(id);
                        stores.strings.resolve(type_info.name)
                    })
                });
            write!(&mut message, "`{a}` and `{b}`").unwrap();
        }
        [xs @ .., last] => {
            for x in xs {
                let kind = analyzer.value_types([*x]).map_or("Unknown", |[v]| {
                    let type_info = stores.types.get_type_info(v);
                    stores.strings.resolve(type_info.name)
                });
                write!(&mut message, "`{kind}`, ").unwrap();
            }

            let kind = analyzer.value_types([*last]).map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.name)
            });
            write!(&mut message, "and `{kind}`").unwrap();
        }
    }

    let mut bad_values = Vec::new();
    for (value_id, order) in types.iter().rev().zip(1..) {
        let value_type = analyzer.value_types([*value_id]).map_or("Unknown", |[v]| {
            let type_info = stores.types.get_type_info(v);
            stores.strings.resolve(type_info.name)
        });
        bad_values.push((*value_id, order, value_type));
    }

    let mut labels =
        diagnostics::build_creator_label_chain(analyzer, bad_values, Color::Yellow, Color::Cyan);
    let op_loc = stores.ops.get_token(op_id).location;
    labels.push(Label::new(op_loc).with_color(Color::Red));
    diagnostics::emit_error(stores, op_loc, message, labels, None);
}

pub(super) fn generate_stack_length_mismatch_diag(
    stores: &Stores,
    sample_location: SourceLocation,
    error_location: SourceLocation,
    actual: usize,
    expected: usize,
    note: impl Into<Option<String>>,
) {
    let message = format!("expected {expected} items, found {actual}");

    let labels = if sample_location != error_location {
        let expected_suffix = if expected == 1 { "" } else { "s" };
        let actual_suffix = if actual == 1 { "" } else { "s" };
        vec![
            Label::new(sample_location)
                .with_color(Color::Cyan)
                .with_message(format!("{expected} value{expected_suffix} here...",))
                .with_order(1),
            Label::new(error_location)
                .with_color(Color::Red)
                .with_message(format!("... but found {actual} value{actual_suffix} here")),
        ]
    } else {
        vec![Label::new(error_location)
            .with_color(Color::Red)
            .with_message("here")]
    };

    diagnostics::emit_error(stores, sample_location, message, labels, note);
}
