use std::{collections::HashMap, fmt::Display};

use intcast::IntCast;
use smallvec::SmallVec;
use stores::{items::ItemId, source::SourceLocation};

use crate::{
    ir::{NameResolvedOp, OpCode, PartiallyResolvedOp, TypeResolvedOp, UnresolvedOp},
    n_ops::ToSmallVec,
    option::OptionExt,
};

use super::values::ValueId;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(u32);

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Op")?;
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct OpIoValues {
    pub inputs: SmallVec<[ValueId; 8]>,
    pub outputs: SmallVec<[ValueId; 8]>,
}

impl OpIoValues {
    #[inline]
    pub fn inputs(&self) -> &[ValueId] {
        self.inputs.as_ref()
    }

    #[inline]
    pub fn outputs(&self) -> &[ValueId] {
        self.outputs.as_ref()
    }
}

pub struct OpStore {
    tokens: Vec<SourceLocation>,
    unresolved: Vec<OpCode<UnresolvedOp>>,
    name_resolved: Vec<Option<OpCode<NameResolvedOp>>>,
    partial_type_resolved: Vec<Option<OpCode<PartiallyResolvedOp>>>,
    type_resolved: Vec<Option<OpCode<TypeResolvedOp>>>,
    op_io: Vec<Option<OpIoValues>>,
    method_callee_ids: HashMap<OpId, ItemId>,
}

impl OpStore {
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            unresolved: Vec::new(),
            name_resolved: Vec::new(),
            partial_type_resolved: Vec::new(),
            type_resolved: Vec::new(),
            op_io: Vec::new(),
            method_callee_ids: HashMap::new(),
        }
    }

    pub fn new_op(&mut self, code: OpCode<UnresolvedOp>, token: SourceLocation) -> OpId {
        let new_id = OpId(self.unresolved.len().to_u32().expect("ICE: OpID overflow"));

        self.unresolved.push(code);
        self.name_resolved.push(None);
        self.partial_type_resolved.push(None);
        self.type_resolved.push(None);
        self.op_io.push(None);
        self.tokens.push(token);

        new_id
    }

    #[inline]
    #[track_caller]
    pub fn get_token_location(&self, id: OpId) -> SourceLocation {
        self.tokens[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_unresolved(&self, id: OpId) -> &OpCode<UnresolvedOp> {
        &self.unresolved[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_name_resolved(&self, id: OpId) -> &OpCode<NameResolvedOp> {
        self.name_resolved[id.0.to_usize()]
            .as_ref()
            .expect("ICE: Tried to get name resolved on an un-resolved item")
    }

    #[inline]
    #[track_caller]
    pub fn set_name_resolved(&mut self, id: OpId, op: OpCode<NameResolvedOp>) {
        self.name_resolved[id.0.to_usize()]
            .replace(op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn get_partially_type_resolved(&self, id: OpId) -> &OpCode<PartiallyResolvedOp> {
        self.partial_type_resolved[id.0.to_usize()]
            .as_ref()
            .expect("ICE: Tried to get partially-type resolved on an un-resolved item")
    }

    #[inline]
    #[track_caller]
    pub fn set_partially_type_resolved(&mut self, id: OpId, op: OpCode<PartiallyResolvedOp>) {
        self.partial_type_resolved[id.0.to_usize()]
            .replace(op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn get_type_resolved(&self, id: OpId) -> &OpCode<TypeResolvedOp> {
        self.type_resolved[id.0.to_usize()]
            .as_ref()
            .expect("ICE: Tried to get type resolved on an un-resolved item")
    }

    #[inline]
    #[track_caller]
    pub fn set_type_resolved(&mut self, id: OpId, op: OpCode<TypeResolvedOp>) {
        self.type_resolved[id.0.to_usize()]
            .replace(op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn overwrite_type_resolved(&mut self, id: OpId, op: OpCode<TypeResolvedOp>) {
        self.type_resolved[id.0.to_usize()] = Some(op);
    }

    #[track_caller]
    pub fn set_op_io(&mut self, op_id: OpId, inputs: impl ToSmallVec, outputs: impl ToSmallVec) {
        let new_data = OpIoValues {
            inputs: inputs.into_smallvec(),
            outputs: outputs.into_smallvec(),
        };
        let prev = &mut self.op_io[op_id.0.to_usize()];
        if let Some(prev) = prev {
            panic!("Set operands twice - cur_token: {op_id}, new_data: {new_data:#?}, prev_data: {prev:#?}");
        }
        *prev = Some(new_data);
    }

    #[inline]
    #[track_caller]
    pub fn get_op_io(&self, op_idx: OpId) -> &OpIoValues {
        self.op_io[op_idx.0.to_usize()]
            .as_ref()
            .expect("ICE: Tried to get unset op-io")
    }

    #[inline]
    #[track_caller]
    pub fn update_op_inputs(&mut self, op_idx: OpId, inputs: &[ValueId]) {
        let existing = self.op_io[op_idx.0.to_usize()]
            .as_mut()
            .expect("ICE: Updated non-existant OP IO");

        existing.inputs.clear();
        existing.inputs.extend_from_slice(inputs);
    }

    #[inline]
    pub fn get_method_callee(&self, id: OpId) -> Option<ItemId> {
        self.method_callee_ids.get(&id).copied()
    }

    #[inline]
    #[track_caller]
    pub fn set_method_callee(&mut self, id: OpId, callee: ItemId) {
        self.method_callee_ids
            .insert(id, callee)
            .expect_none("ICE: Set method callee twice");
    }
}
