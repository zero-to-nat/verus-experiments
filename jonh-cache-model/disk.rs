use vstd::prelude::*;
use crate::frac::*;

verus!{

pub struct Disk {
    block_count: usize,
    frac_ids: Ghost<Map<usize, int>>,
}

impl Disk {
    pub closed spec fn id(self, lba: usize) -> int
    {
        self.frac_ids@[lba]
    }

    pub fn new(block_count: usize) -> (out: (Self, Tracked<Map<usize, Frac<Seq<u8>>>>))
    ensures
        forall |lba| 0<=lba<block_count <==> out.1@.contains_key(lba),
        forall |lba| #![auto] 0<=lba<block_count ==> out.1@[lba].id() == out.0.id(lba),
    {
        assume(false);
        unreached()
    }

    pub fn read(&self, lba: usize, top: &Tracked<Frac<Seq<u8>>>) -> (out: Vec<u8>)
    requires
        top@.valid(self.id(lba), 1),
    ensures
        out@ == top@@
    {
        assume(false);
        unreached()
    }

    pub fn write(&self, lba: usize, top: &mut Tracked<Frac<Seq<u8>>>, value: Vec<u8>)
    requires
        old(top)@.valid(self.id(lba), 1),
    ensures
        top@.valid(self.id(lba), 1),
        top@@ == value@,
    {
        assume(false);
    }
}

}//verus!
