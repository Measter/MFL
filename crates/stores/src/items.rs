use intcast::IntCast;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(u32);

impl std::fmt::Debug for ItemId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ItemId({})", self.0)
    }
}

impl ItemId {
    pub fn new(id: u32) -> Self {
        Self(id)
    }
    pub fn to_usize(self) -> usize {
        self.0.to_usize()
    }
}
