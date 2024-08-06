use intcast::IntCast;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(u16);

impl ItemId {
    pub fn new(id: u16) -> Self {
        Self(id)
    }
    pub fn to_usize(self) -> usize {
        self.0.to_usize()
    }
}
