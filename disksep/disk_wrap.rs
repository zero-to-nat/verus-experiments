use vstd::prelude::*;
use super::disk::*;
use super::seq_view::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<SeqAuth<u8>>,
        pa: Tracked<SeqAuth<u8>>,
    }

    impl DiskWrap {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.d.inv()
            &&& self.a@.inv()
            &&& self.pa@.inv()
            &&& self.d@ =~= self.a@@
            &&& self.d.persist() =~= self.pa@@
        }

        pub closed spec fn id(self) -> int
        {
            self.a@.id()
        }

        pub closed spec fn persist_id(self) -> int
        {
            self.pa@.id()
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

        pub fn write(&mut self, a: usize, v: &[u8],
                     Tracked(perm): Tracked<&mut SeqFrac<u8>>,
                     Tracked(pperm): Tracked<&mut SeqFrac<u8>>)
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                old(perm).off() == a,
                old(perm)@.len() == v@.len(),
                old(pperm).valid(old(self).persist_id()),
                old(pperm).off() == a,
                old(pperm)@.len() == v@.len(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.persist_id() == old(self).persist_id(),
                perm.valid(self.id()),
                perm.off() == old(perm).off(),
                perm@ =~= v@,
                pperm.valid(self.persist_id()),
                pperm.off() == old(pperm).off(),
                can_result_from_write(pperm@, old(pperm)@, 0, v@),
        {
            proof {
                perm.agree(self.a.borrow());
                pperm.agree(self.pa.borrow());
            }
            self.d.write(a, v);
            proof {
                perm.update(self.a.borrow_mut(), v@);
                pperm.update(self.pa.borrow_mut(), self.d.persist().subrange(a as int, a+v.len()));
            }
        }

        pub fn new(d: Disk) -> (result: (DiskWrap, Tracked<SeqFrac<u8>>, Tracked<SeqFrac<u8>>))
            requires
                d.inv(),
                d@.len() > 0,
                d.persist().len() > 0,
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id()),
                result.1@.off() == 0,
                result.1@@ == d@,
                result.2@.valid(result.0.persist_id()),
                result.2@.off() == 0,
                result.2@@ == d.persist(),
        {
            let tracked (ar, fr) = SeqAuth::<u8>::new(d@);
            let tracked (par, pfr) = SeqAuth::<u8>::new(d.persist());
            let dw = DiskWrap{
                d: d,
                a: Tracked(ar),
                pa: Tracked(par),
            };
            (dw, Tracked(fr), Tracked(pfr))
        }
    }
}
