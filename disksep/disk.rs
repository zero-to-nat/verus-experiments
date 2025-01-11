use std::collections::HashMap;
use vstd::prelude::*;

verus! {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    pub struct Disk {
        store: HashMap<u64, u8>,
    }

    impl Disk {
        pub closed spec fn view(&self) -> Map<u64, u8>
        {
            self.store@
        }

        pub fn read(&self, a: u64) -> (result: u8)
            requires
                self@.contains_key(a)
            ensures
                result == self@[a]
        {
            *self.store.get(&a).unwrap()
        }

        pub fn write(&mut self, a: u64, v: u8)
            requires
                old(self)@.dom().contains(a)
            ensures
                self@ == old(self)@.insert(a, v)
        {
            self.store.insert(a, v);
            ()
        }
    }
}
