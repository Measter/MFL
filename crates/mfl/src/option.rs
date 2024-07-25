pub trait OptionExt {
    fn expect_none(self, msg: &str);
}

impl<T> OptionExt for Option<T> {
    #[inline]
    fn expect_none(self, msg: &str) {
        assert!(self.is_none(), "{msg}");
    }
}
