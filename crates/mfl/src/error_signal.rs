pub struct ErrorSignal(bool);

impl ErrorSignal {
    pub fn new() -> Self {
        Self(false)
    }

    pub fn set(&mut self) {
        self.0 = true;
    }

    pub fn merge_with(&mut self, rhs: Self) {
        self.0 |= rhs.0;
        std::mem::forget(rhs);
    }

    pub fn into_err(self) -> bool {
        let b = self.0;
        std::mem::forget(self);
        b
    }

    pub fn is_ok(&self) -> bool {
        let Self(b) = self;
        !b
    }

    pub fn forget(self) {
        std::mem::forget(self);
    }
}

impl Drop for ErrorSignal {
    #[track_caller]
    fn drop(&mut self) {
        panic!("ICE: Unhandled error signal");
    }
}
