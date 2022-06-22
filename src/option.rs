pub trait OptionExt {
    fn expect_none(self, msg: &str);
}

impl<T> OptionExt for Option<T> {
    fn expect_none(self, msg: &str) {
        if self.is_some() {
            panic!("{}", msg)
        }
    }
}
