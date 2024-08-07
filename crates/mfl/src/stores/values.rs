use std::fmt::{Display, Write};

use hashbrown::HashMap;
use intcast::IntCast;
use smallvec::SmallVec;
use stores::{items::ItemId, source::SourceLocation};

use crate::{n_ops::HashMapNOps, option::OptionExt};

use super::{
    ops::OpId,
    types::{Float, Integer, TypeId},
};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueId(u32);

impl Display for ValueId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VId")?;
        self.0.fmt(f)?;
        f.write_char('_')
    }
}

#[derive(Debug, Clone)]
pub struct Value {
    pub source_location: SourceLocation,
    pub parent_value: Option<ValueId>,
    pub consumer: SmallVec<[OpId; 4]>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConstVal {
    Int(Integer),
    Float(Float),
    Bool(bool),
    MultiPtr {
        source_variable: ItemId,
        offset: Option<u64>,
    },
    SinglePtr {
        source_variable: ItemId,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct MergeValue {
    pub a_in: ValueId,
    pub b_in: ValueId,
    pub out: ValueId,
}

#[derive(Debug, Clone, Default)]
pub struct ValueStore {
    value_lifetime: HashMap<ValueId, Value>,
    value_types: HashMap<ValueId, TypeId>,
    value_consts: HashMap<ValueId, ConstVal>,

    op_merges: HashMap<OpId, Vec<MergeValue>>,
}

impl ValueStore {
    pub fn new() -> Self {
        Self {
            value_lifetime: HashMap::default(),
            value_types: HashMap::default(),
            value_consts: HashMap::default(),
            op_merges: HashMap::default(),
        }
    }

    pub fn new_value(
        &mut self,
        source_location: SourceLocation,
        parent_value: Option<ValueId>,
    ) -> ValueId {
        let id = self.value_lifetime.len();
        let id = ValueId(id.to_u32().unwrap());

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

    pub fn values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.value_lifetime[&id])
    }

    pub fn consume_value(&mut self, value: ValueId, consumer_id: OpId) {
        let val = self.value_lifetime.get_mut(&value).unwrap();
        val.consumer.push(consumer_id);
    }

    pub fn value_types<const N: usize>(&self, ids: [ValueId; N]) -> Option<[TypeId; N]> {
        self.value_types.get_n(ids)
    }

    pub fn set_value_type(&mut self, id: ValueId, kind: TypeId) {
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

    pub fn set_merge_values(&mut self, op_id: OpId, merges: Vec<MergeValue>) {
        self.op_merges
            .insert(op_id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    pub fn get_merge_values(&self, op_id: OpId) -> Option<&Vec<MergeValue>> {
        self.op_merges.get(&op_id)
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
