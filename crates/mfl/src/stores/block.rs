use std::fmt::Display;

use intcast::IntCast;

use super::ops::OpId;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BlockId(u32);

impl Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Block")?;
        self.0.fmt(f)
    }
}
#[derive(Debug, Clone)]
pub struct Block {
    pub ops: Vec<OpId>,
}

pub struct BlockStore {
    blocks: Vec<Block>,
    is_terminal: Vec<bool>,
}

impl BlockStore {
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            is_terminal: Vec::new(),
        }
    }

    pub fn new_block(&mut self, ops: Vec<OpId>) -> BlockId {
        let new_id = BlockId(self.blocks.len().to_u32().expect("ICE: Block ID overflow"));
        self.is_terminal.push(false);
        self.blocks.push(Block { ops });

        new_id
    }

    pub fn get_block(&self, id: BlockId) -> &Block {
        &self.blocks[id.0.to_usize()]
    }

    pub fn is_terminal(&self, id: BlockId) -> bool {
        self.is_terminal[id.0.to_usize()]
    }

    pub fn set_terminal(&mut self, id: BlockId) {
        self.is_terminal[id.0.to_usize()] = true;
    }
}
