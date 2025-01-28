use vstd::prelude::*;
use crate::frac::*;

verus!{

pub struct Disk {
    block_count: usize,
    frac_ids: Ghost<Map<usize, int>>,
}

pub open spec fn set_range(len: int) -> (s: Set<int>)
decreases len when 0 <= len
{
    if len==0 { Set::empty() }  else { set_range(len-1).insert(len-1) }
}

pub proof fn set_range_properties(len: int)
requires 0 <= len
ensures 
    set_range(len).finite(),
    set_range(len).len() == len,
    forall |i: int| 0 <= i < len <==> set_range(len).contains(i),
decreases len
{
    if 0<len { set_range_properties(len-1); }
}

pub open spec fn usize_set_range(len: usize) -> (s: Set<usize>)
{
    Set::new(|x: usize| set_range(len as int).contains(x as int))
}

impl Disk {
    pub closed spec fn id(self, lba: usize) -> int
    {
        self.frac_ids@[lba]
    }

    pub closed spec fn block_count(self) -> usize
    {
        self.block_count
    }

    pub fn new(block_count: usize) -> (out: (Self, Tracked<Map<usize, Frac<Seq<u8>>>>))
    ensures
        out.1@.dom().finite(),
        out.1@.dom() == usize_set_range(block_count),
        out.0.block_count() == block_count,
//        forall |lba| 0<=lba<block_count <==> out.1@.contains_key(lba),
        forall |lba| #![auto] 0<=lba<block_count ==> out.1@[lba].id() == out.0.id(lba),
        forall |lba| out.1@.contains_key(lba) ==> out.1@[lba].valid(out.0.id(lba), 1),
    {
        assume(false);
        unreached()
    }

    pub fn read(&self, lba: usize, top: Tracked<&Frac<Seq<u8>>>) -> (out: Vec<u8>)
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
