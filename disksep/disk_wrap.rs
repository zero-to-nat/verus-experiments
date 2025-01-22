use vstd::prelude::*;
use super::disk::*;
use super::seq_view::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<SeqAuth<u8>>,
    }

    impl DiskWrap {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.d.inv()
            &&& self.a@.inv()
            &&& self.d@ =~= self.a@@
        }

        pub closed spec fn id(self) -> int
        {
            self.a@.id()
        }

        pub fn read(&self, a: usize, len: usize, Tracked(perm): Tracked<&SeqFrac<u8>>) -> (result: Vec<u8>)
            requires
                self.inv(),
                perm.valid(self.id()),
                perm.off() == a,
                perm@.len() == len,
            ensures
                result@ =~= perm@,
        {
            proof {
                perm.agree(self.a.borrow());
            }
            self.d.read(a, len)
        }

        pub fn write(&mut self, a: usize, v: &[u8], Tracked(perm): Tracked<&mut SeqFrac<u8>>)
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                old(perm).off() == a,
                old(perm)@.len() == v@.len(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.valid(self.id()),
                perm.off() == old(perm).off(),
                perm@ =~= v@,
        {
            proof {
                perm.agree(self.a.borrow());
            }
            self.d.write(a, v);
            proof {
                perm.update(self.a.borrow_mut(), v@);
            }
        }

        pub fn new(d: Disk) -> (result: (DiskWrap, Tracked<SeqFrac<u8>>))
            requires
                d.inv(),
                d@.len() > 0,
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id()),
                result.1@.off() == 0,
                result.1@@ == d@,
        {
            let tracked (ar, fr) = SeqAuth::<u8>::new(d@);
            (DiskWrap{ d: d, a: Tracked(ar) }, Tracked(fr))
        }
    }
}
