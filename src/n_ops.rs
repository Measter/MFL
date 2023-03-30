use std::{hash::Hash, mem::MaybeUninit};

use hashbrown::HashMap;

pub trait VecNOps<T> {
    fn popn<const N: usize>(&mut self) -> Option<[T; N]>;
}

impl<T> VecNOps<T> for Vec<T> {
    fn popn<const N: usize>(&mut self) -> Option<[T; N]> {
        assert!(N > 0);
        if self.len() < N {
            return None;
        }

        // SAFETY: We know the Vec has enough elements, so we won't be accessing uninitialized data.
        unsafe {
            let mut dest: MaybeUninit<[T; N]> = MaybeUninit::uninit();
            let dest_ptr = dest.as_mut_ptr() as *mut T;
            let stack_ptr = self.as_mut_ptr().add(self.len() - N);

            std::ptr::copy_nonoverlapping(stack_ptr, dest_ptr, N);

            self.set_len(self.len() - N);

            Some(dest.assume_init())
        }
    }
}

pub trait SliceNOps<T> {
    fn lastn(&self, n: usize) -> Option<&Self>;
    fn lastn_mut(&mut self, n: usize) -> Option<&mut Self>;
    fn as_arr<const N: usize>(&self) -> &[T; N];
}

impl<T> SliceNOps<T> for [T] {
    fn lastn(&self, n: usize) -> Option<&Self> {
        if self.len() < n {
            return None;
        }
        Some(&self[self.len() - n..])
    }

    fn lastn_mut(&mut self, n: usize) -> Option<&mut Self> {
        if self.len() < n {
            return None;
        }
        let len = self.len();
        Some(&mut self[len - n..])
    }

    #[track_caller]
    fn as_arr<const N: usize>(&self) -> &[T; N] {
        self.try_into().unwrap()
    }
}

pub trait HashMapNOps<K, V> {
    fn get_n<const N: usize>(&self, keys: [K; N]) -> Option<[V; N]>;
}

impl<K, V> HashMapNOps<K, V> for HashMap<K, V>
where
    K: Hash + Eq,
    V: Copy,
{
    fn get_n<const N: usize>(&self, keys: [K; N]) -> Option<[V; N]> {
        assert!(N > 0);

        // SAFETY: Because V is Copy, and therefore cannot have a Drop implementation,
        // we don't need to specially handle dropping a partially initialized array
        // and can just return None if a key doesn't exist.
        unsafe {
            let mut dest = [MaybeUninit::<V>::uninit(); N];

            for (dst, id) in dest.iter_mut().zip(keys) {
                dst.write(*self.get(&id)?);
            }

            Some(std::mem::transmute_copy(&dest))
        }
    }
}
