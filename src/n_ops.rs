use std::mem::MaybeUninit;

use hashbrown::HashMap;

pub trait VecNOps<T> {
    fn popn<const N: usize>(&mut self) -> Option<[T; N]>;
    fn popn_last_mut<const N: usize>(&mut self) -> Option<([T; N], &mut T)>;
}

impl<T> VecNOps<T> for Vec<T> {
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

            Some(dest.assume_init())
        }
    }

    fn popn_last_mut<const N: usize>(&mut self) -> Option<([T; N], &mut T)> {
        if self.len() < N + 1 {
            return None;
        }

        let popped = self.popn().unwrap();
        let last = self.last_mut().unwrap();
        Some((popped, last))
    }
}

pub trait SliceNOps<T> {
    fn firstn<const N: usize>(&self) -> Option<(&[T; N], &Self)>;
    fn lastn(&self, n: usize) -> Option<&Self>;
    fn as_arr<const N: usize>(&self) -> &[T; N];
}

impl<T> SliceNOps<T> for [T] {
    fn firstn<const N: usize>(&self) -> Option<(&[T; N], &Self)> {
        assert!(N > 0);
        if self.len() < N {
            return None;
        }

        let (start, rest) = self.split_at(N);
        Some((start.try_into().ok()?, rest))
    }

    fn lastn(&self, n: usize) -> Option<&Self> {
        if self.len() < n {
            return None;
        }
        Some(&self[self.len() - n..])
    }

    fn as_arr<const N: usize>(&self) -> &[T; N] {
        self.try_into().unwrap()
    }
}
