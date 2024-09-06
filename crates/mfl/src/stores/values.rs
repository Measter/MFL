use std::fmt::{Display, Write};

use hashbrown::HashMap;
use intcast::IntCast;
use smallvec::SmallVec;
use stores::{items::ItemId, source::SourceLocation};

use crate::{n_ops::HashMapNOps, option::OptionExt};

use super::{
    block::BlockId,
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
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConstVal {
    Uninitialized,
    Unknown,
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

#[derive(Debug, Clone)]
pub struct MergeValue {
    // BlockId = Arm which produced the value.
    pub inputs: Vec<(BlockId, ValueId)>,
    pub output: ValueId,
}

impl MergeValue {
    pub fn block_input(&self, block_id: BlockId) -> Option<ValueId> {
        self.inputs
            .iter()
            .find(|(blk, _l)| *blk == block_id)
            .map(|(_, v)| *v)
    }
}

#[derive(Debug, Clone, Default)]
pub struct ValueStore {
    value_lifetime: Vec<Value>,
    value_types: HashMap<ValueId, TypeId>,
    value_consts: Vec<ConstVal>,

    op_merges: HashMap<OpId, Vec<MergeValue>>,
}

impl ValueStore {
    pub fn new() -> Self {
        Self {
            value_lifetime: Vec::new(),
            value_types: HashMap::default(),
            value_consts: Vec::new(),
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

        self.value_lifetime.push(Value {
            source_location,
            parent_value,
        });

        self.value_consts.push(ConstVal::Unknown);

        id
    }

    pub fn value_count(&self) -> usize {
        self.value_lifetime.len()
    }

    pub fn values<const N: usize>(&self, ids: [ValueId; N]) -> [&Value; N] {
        ids.map(|id| &self.value_lifetime[id.0.to_usize()])
    }

    pub fn value_types<const N: usize>(&self, ids: [ValueId; N]) -> Option<[TypeId; N]> {
        self.value_types.get_n(ids)
    }

    #[track_caller]
    pub fn set_value_type(&mut self, id: ValueId, kind: TypeId) {
        self.value_types
            .insert(id, kind)
            .expect_none("ICE: Tried to set a value type twice");
    }

    pub fn value_consts<const N: usize>(&self, ids: [ValueId; N]) -> [ConstVal; N] {
        ids.map(|i| self.value_consts[i.0.to_usize()])
    }

    pub fn set_value_const(&mut self, id: ValueId, const_val: ConstVal) {
        self.value_consts[id.0.to_usize()] = const_val;
    }

    #[track_caller]
    pub fn set_merge_values(&mut self, op_id: OpId, merges: Vec<MergeValue>) {
        merges.iter().for_each(|mv| {
            assert!(
                mv.inputs.len() >= 2,
                "ICE: Created merge value with less than 2 inputs"
            )
        });

        self.op_merges
            .insert(op_id, merges)
            .expect_none("ICE: Tried to overwrite merges");
    }

    #[track_caller]
    pub fn update_marge_values(&mut self, op_id: OpId, merges: Vec<MergeValue>) {
        merges.iter().for_each(|mv| {
            assert!(
                mv.inputs.len() >= 2,
                "ICE: Created merge value with less than 2 inputs"
            )
        });
        self.op_merges.insert(op_id, merges);
    }

    pub fn get_merge_values(&self, op_id: OpId) -> Option<&Vec<MergeValue>> {
        self.op_merges.get(&op_id)
    }

    /// Returns the creator token of a value, treating Dup and Over tokens as transparent.
    pub fn get_creator_token(&self, value_id: ValueId) -> SmallVec<[SourceLocation; 2]> {
        let mut creators = SmallVec::new();

        let value_info = &self.value_lifetime[value_id.0.to_usize()];
        let mut cur_creator = value_info.parent_value;
        creators.push(value_info.source_location);

        while let Some(parent) = cur_creator {
            let value_info = &self.value_lifetime[parent.0.to_usize()];
            cur_creator = value_info.parent_value;
            creators.push(value_info.source_location);
        }

        creators
    }
}
