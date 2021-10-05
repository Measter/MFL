use std::mem::MaybeUninit;

pub trait PopN<T> {
    fn popn<const N: usize>(&mut self) -> Option<[T; N]>;
}

impl<T> PopN<T> for Vec<T> {
    fn popn<const N: usize>(&mut self) -> Option<[T; N]> {
        assert!(N > 0);
        if self.len() < N {
            return None;
        }

        unsafe {
            let mut dest: MaybeUninit<[T; N]> = MaybeUninit::uninit();
            let dest_ptr = dest.as_mut_ptr() as *mut T;
            let stack_ptr = self.as_mut_ptr().add(self.len() - N);

            std::ptr::copy_nonoverlapping(stack_ptr, dest_ptr, N);

            self.set_len(self.len() - N);

            let mut dest = dest.assume_init();
            dest.reverse();
            Some(dest)
        }
    }
}