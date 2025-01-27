use vstd::prelude::*;
use super::vecdisk::*;
use super::seq_view::*;
use super::logatom::*;

verus! {
    pub struct DiskResources {
        pub latest: SeqAuth<u8>,
        pub persist: SeqAuth<u8>,
    }

    pub struct DiskWrap {
        d: Disk,
        r: Tracked<DiskResources>,
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
            &&& r.valid(self.persist_id)
            &&& can_result_from_write(pstate, r@.subrange(self.addr as int, self.addr+self.data.len()), 0, self.data)
        }

        open spec fn ensures(self, pstate: Seq<u8>, pre: Self::Resource, post: Self::Resource) -> bool {
            &&& post.valid(self.persist_id)
            &&& post@ == update_bytes(pre@, self.addr as int, pstate)
        }
    }

    pub struct FlushOp {
        pub id: int,
        pub persist_id: int,
    }

    impl ReadOperation for FlushOp {
        type Resource = DiskResources;
        type ExecResult = ();

        open spec fn requires(self, r: Self::Resource, e: ()) -> bool {
            &&& r.latest.valid(self.id)
            &&& r.persist.valid(self.persist_id)
            &&& r.latest@ == r.persist@
        }
    }

    pub struct ValidateOp {
        pub id: int,
        pub addr: usize,
        pub len: usize,
    }

    impl ReadOperation for ValidateOp {
        type Resource = SeqAuth<u8>;
        type ExecResult = ();

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id)
        }

        open spec fn ensures(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& self.addr + self.len <= r@.len()
        }
    }

    pub struct ReadOp {
        pub id: int,
        pub addr: usize,
        pub len: usize,
    }

    impl ReadOperation for ReadOp {
        type Resource = SeqAuth<u8>;
        type ExecResult = Vec<u8>;

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id)
            &&& e@ == r@.subrange(self.addr as int, self.addr + self.len as int)
        }
    }

    impl DiskWrap {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.d.inv()
            &&& self.r@.latest.inv()
            &&& self.r@.persist.inv()
            &&& self.r@.latest@ =~= self.d@
            &&& self.r@.persist@ =~= self.d.persist()
            &&& self.r@.latest@.len() == self.r@.persist@.len()
        }

        pub closed spec fn id(self) -> int
        {
            self.r@.latest.id()
        }

        pub closed spec fn persist_id(self) -> int
        {
            self.r@.persist.id()
        }

        pub fn read<Validate, Lin>(&self, a: usize, len: usize, Tracked(validate): Tracked<Validate>, Tracked(lin): Tracked<Lin>) -> (result: (Vec<u8>, Tracked<Lin::ApplyResult>))
            where
                Validate: ReadLinearizer<ValidateOp>,
                Lin: ReadLinearizer<ReadOp>,
            requires
                self.inv(),
                validate.pre(ValidateOp{ id: self.id(), addr: a, len: len }),
                lin.pre(ReadOp{ id: self.id(), addr: a, len: len }),
            ensures
                lin.post(ReadOp{ id: self.id(), addr: a, len: len }, result.0, result.1@),
        {
            proof {
                validate.apply(ValidateOp{ id: self.id(), addr: a, len: len }, &self.r.borrow().latest, &());
            }
            let r = self.d.read(a, len);
            let lin_r = Tracked(lin.apply(ReadOp{ id: self.id(), addr: a, len: len }, &self.r.borrow().latest, &r));
            (r, lin_r)
        }

        pub fn write<Lin>(&mut self, a: usize, v: &[u8],
                          Tracked(perm): Tracked<&mut SeqFrac<u8>>,
                          Tracked(p_lin): Tracked<Lin>) -> (result: Tracked<Lin::ApplyResult>)
            where
                Lin: MutLinearizer<WriteOp>,
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                old(perm).off() == a,
                old(perm)@.len() == v@.len(),
                p_lin.pre(WriteOp{ persist_id: old(self).persist_id(), addr: a, data: v@ }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.persist_id() == old(self).persist_id(),
                perm.valid(self.id()),
                perm.off() == old(perm).off(),
                perm@ =~= v@,
                p_lin.post(WriteOp{ persist_id: old(self).persist_id(), addr: a, data: v@ }, (), result@),
        {
            proof {
                perm.agree(&self.r.borrow().latest);
            }
            self.d.write(a, v);
            Tracked({
                perm.update(&mut self.r.borrow_mut().latest, v@);
                p_lin.apply(WriteOp{ persist_id: old(self).persist_id(), addr: a, data: v@ }, self.d.persist().subrange(a as int, a+v.len()), &mut self.r.borrow_mut().persist, &())
            })
        }

        pub fn flush<Lin>(&self, Tracked(p_lin): Tracked<Lin>) -> (result: Tracked<Lin::ApplyResult>)
            where
                Lin: ReadLinearizer<FlushOp>,
            requires
                self.inv(),
                p_lin.pre(FlushOp{ id: self.id(), persist_id: self.persist_id() }),
            ensures
                p_lin.post(FlushOp{ id: self.id(), persist_id: self.persist_id() }, (), result@),
        {
            self.d.flush();
            Tracked({
                p_lin.apply(FlushOp{ id: self.id(), persist_id: self.persist_id() }, self.r.borrow(), &())
            })
        }

        pub fn new(d: Disk) -> (result: (DiskWrap, Tracked<SeqFrac<u8>>, Tracked<SeqFrac<u8>>))
            requires
                d.inv(),
                d@.len() > 0,
                d.persist().len() == d@.len(),
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
                r: Tracked(DiskResources{
                    latest: ar,
                    persist: par,
                }),
            };
            (dw, Tracked(fr), Tracked(pfr))
        }
    }
}
