use vstd::prelude::*;

verus! {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    pub struct Disk {
        store: Vec<u8>,
    }

    impl Disk {
        pub closed spec fn view(&self) -> Seq<u8>
        {
            self.store@
        }

        pub fn read(&self, a: usize) -> (result: u8)
            requires
                a < self@.len()
            ensures
                result == self@[a as int]
        {
            self.store[a]
        }

        pub fn write(&mut self, a: usize, v: u8)
            requires
                a < old(self)@.len()
            ensures
                self@ == old(self)@.update(a as int, v)
        {
            // XXX Where is Vec::set() coming from?
            self.store.set(a, v);
        }
    }
}
