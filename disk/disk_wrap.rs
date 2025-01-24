use vstd::prelude::*;
use super::vecdisk::*;
use super::seq_view::*;
use super::logatom::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<SeqAuth<u8>>,
        pa: Tracked<SeqAuth<u8>>,
    }

    pub struct WriteOp {
        pub persist_id: int,
        pub addr: usize,
        pub data: Seq<u8>,
    }

    impl MutOperation for WriteOp {
        type Resource = SeqAuth<u8>;
        type ExecResult = ();
        type ApplyHint = Seq<u8>;

        open spec fn requires(self, pstate: Seq<u8>, r: Self::Resource, e: ()) -> bool {
            &&& r.inv()
            &&& r.id() == self.persist_id
            &&& can_result_from_write(pstate, r@, self.addr as int, self.data)
        }

        open spec fn ensures(self, pstate: Seq<u8>, pre: Self::Resource, post: Self::Resource) -> bool {
            &&& post.inv()
            &&& post.id() == self.persist_id
            &&& post@ == pstate
        }
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

        pub fn write<Op>(&mut self, a: usize, v: &[u8],
                         Tracked(perm): Tracked<&mut SeqFrac<u8>>,
                         Tracked(p_op): Tracked<Op>) -> (result: Tracked<Op::ApplyResult>)
            where
                Op: MutLinearizer<WriteOp>,
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                old(perm).off() == a,
                old(perm)@.len() == v@.len(),
                p_op.pre(WriteOp{ persist_id: old(self).persist_id(), addr: a, data: v@ }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.persist_id() == old(self).persist_id(),
                perm.valid(self.id()),
                perm.off() == old(perm).off(),
                perm@ =~= v@,
                p_op.post(WriteOp{ persist_id: old(self).persist_id(), addr: a, data: v@ }, (), result@),
        {
            proof {
                perm.agree(self.a.borrow());
            }
            self.d.write(a, v);
            Tracked({
                perm.update(self.a.borrow_mut(), v@);
                p_op.apply(WriteOp{ persist_id: old(self).persist_id(), addr: a, data: v@ }, self.d.persist(), self.pa.borrow_mut(), &())
            })
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
