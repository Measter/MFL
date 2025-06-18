use std::{collections::HashMap, fmt::Display};

use intcast::IntCast;
use smallvec::SmallVec;
use stores::{items::ItemId, source::SourceLocation};

use crate::{
    ir::{NameResolvedOp, OpCode, PartiallyResolvedOp, TypeResolvedOp, UnresolvedOp},
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
    name_resolved: HashMap<OpId, OpCode<NameResolvedOp>>,
    partial_type_resolved: HashMap<OpId, OpCode<PartiallyResolvedOp>>,
    type_resolved: HashMap<OpId, OpCode<TypeResolvedOp>>,
    op_io: HashMap<OpId, OpIoValues>,
    method_callee_ids: HashMap<OpId, ItemId>,
}

impl OpStore {
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            unresolved: Vec::new(),
            name_resolved: HashMap::new(),
            partial_type_resolved: HashMap::new(),
            type_resolved: HashMap::new(),
            op_io: HashMap::new(),
            method_callee_ids: HashMap::new(),
        }
    }

    pub fn new_op(&mut self, code: OpCode<UnresolvedOp>, token: SourceLocation) -> OpId {
        let new_id = OpId(self.unresolved.len().to_u32().expect("ICE: OpID overflow"));

        self.unresolved.push(code);
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
        &self.name_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_name_resolved(&mut self, id: OpId, op: OpCode<NameResolvedOp>) {
        self.name_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn get_partially_type_resolved(&self, id: OpId) -> &OpCode<PartiallyResolvedOp> {
        &self.partial_type_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_partially_type_resolved(&mut self, id: OpId, op: OpCode<PartiallyResolvedOp>) {
        self.partial_type_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn get_type_resolved(&self, id: OpId) -> &OpCode<TypeResolvedOp> {
        &self.type_resolved[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_type_resolved(&mut self, id: OpId, op: OpCode<TypeResolvedOp>) {
        self.type_resolved
            .insert(id, op)
            .expect_none("ICE: Inserted multiple ops at id");
    }

    #[inline]
    #[track_caller]
    pub fn overwrite_type_resolved(&mut self, id: OpId, op: OpCode<TypeResolvedOp>) {
        self.type_resolved.insert(id, op);
    }

    #[track_caller]
    pub fn set_op_io(&mut self, op_id: OpId, inputs: &[ValueId], outputs: &[ValueId]) {
        let new_data = OpIoValues {
            inputs: inputs.into(),
            outputs: outputs.into(),
        };
        if let Some(prev) = self.op_io.get(&op_id) {
            panic!("Set operands twice - cur_token: {op_id}, new_data: {new_data:#?}, prev_data: {prev:#?}");
        }
        self.op_io.insert(op_id, new_data);
    }

    #[inline]
    #[track_caller]
    pub fn get_op_io(&self, op_idx: OpId) -> &OpIoValues {
        &self.op_io[&op_idx]
    }

    #[inline]
    #[track_caller]
    pub fn update_op_inputs(&mut self, op_idx: OpId, inputs: &[ValueId]) {
        let existing = self
            .op_io
            .get_mut(&op_idx)
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
