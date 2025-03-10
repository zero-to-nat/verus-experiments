use std::sync::Arc;

use super::disk::disk_wrap::*;
use super::disk::logatom::*;
use super::disk::seq_view::*;
use super::disk::frac::*;
use super::disk::seq_helper::*;

use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    pub const ptr_addr: usize = 0;
    pub const a_addr: usize = 1;
    pub const b_addr: usize = 3;
    pub const total: u8 = 10;

    pub enum PtrState {
        A,
        B,
        Either,
    }

    pub struct DiskCrashState {
        pub ptr: SeqFrac<u8>,
        pub a: SeqFrac<u8>,
        pub b: SeqFrac<u8>,
        pub ptr_state: Frac<PtrState>,
    }

    pub struct DiskInvParam {
        pub persist_id: int,
        pub ptr_state_id: int,
    }

    impl InvariantPredicate<DiskInvParam, DiskCrashState> for DiskInvParam {
        open spec fn inv(k: DiskInvParam, inner: DiskCrashState) -> bool {
            &&& inner.ptr.valid(k.persist_id)
            &&& inner.ptr.off() == ptr_addr
            &&& inner.ptr@.len() == 1

            &&& inner.ptr_state.valid(k.ptr_state_id, 1)

            &&& inner.a.valid(k.persist_id)
            &&& inner.a.off() == a_addr
            &&& inner.a@.len() == 2

            &&& inner.b.valid(k.persist_id)
            &&& inner.b.off() == b_addr
            &&& inner.b@.len() == 2

            &&& (inner.ptr_state@ == PtrState::A || inner.ptr_state@ == PtrState::Either) ==> inner.a@[0] + inner.a@[1] == total
            &&& (inner.ptr_state@ == PtrState::B || inner.ptr_state@ == PtrState::Either) ==> inner.b@[0] + inner.b@[1] == total

            &&& {
                ||| {
                    &&& inner.ptr@[0] == 0
                    &&& (inner.ptr_state@ == PtrState::A || inner.ptr_state@ == PtrState::Either)
                    }
                ||| {
                    &&& inner.ptr@[0] == 1
                    &&& (inner.ptr_state@ == PtrState::B || inner.ptr_state@ == PtrState::Either)
                    }
                }
        }
    }

    // Writing to a block that's currently unused.
    pub struct InactiveWriter<'a> {
        pub latest_frac: SeqFrac<u8>,
        pub ptr_state_frac: &'a Frac<PtrState>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        pub credit: OpenInvariantCredit,
    }

    impl<'a> MutLinearizer<WriteOp> for InactiveWriter<'a> {
        type ApplyResult = SeqFrac<u8>;

        closed spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: WriteOp) -> bool {
            &&& self.latest_frac.valid(op.id)
            &&& self.latest_frac.off() <= op.addr
            &&& op.addr + op.data.len() <= self.latest_frac.off() + self.latest_frac@.len()

            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& op.persist_id == self.inv.constant().persist_id
            &&& op.data.len() == 2
            &&& {
                ||| op.addr == a_addr && self.ptr_state_frac@ == PtrState::B
                ||| op.addr == b_addr && self.ptr_state_frac@ == PtrState::A
                }
        }

        open spec fn post(self, op: WriteOp, r: (), ar: Self::ApplyResult) -> bool {
            &&& ar.valid(op.id)
            &&& ar.off() == self.latest_frac.off()
            &&& ar@ == update_seq(self.latest_frac@, op.addr - self.latest_frac.off(), op.data)
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut DiskResources, e: &()) -> (tracked result: Self::ApplyResult) {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                mself.ptr_state_frac.agree(&inner.ptr_state);

                if op.addr == a_addr {
                    inner.a.agree(&r.persist);
                    inner.a.update(&mut r.persist, pstate);
                } else {
                    inner.b.agree(&r.persist);
                    inner.b.update(&mut r.persist, pstate);
                }
            });

            mself.latest_frac.agree(&r.latest);
            mself.latest_frac.update_range(&mut r.latest, op.addr - mself.latest_frac.off(), op.data);

            mself.latest_frac
        }

        proof fn peek(tracked &self, op: WriteOp, tracked r: &DiskResources) {
            self.latest_frac.agree(&r.latest);
        }
    }

    impl<'a> InactiveWriter<'a> {
        pub fn new(Tracked(lf): Tracked<SeqFrac<u8>>, Tracked(ps): Tracked<&'a Frac<PtrState>>,
               Tracked(i): Tracked<&Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>>) -> (result: Tracked<Self>)
            ensures
                result@.latest_frac == lf,
                result@.ptr_state_frac == ps,
                result@.inv == i,
        {
            let credit = create_open_invariant_credit();
            Tracked(Self{
                latest_frac: lf,
                ptr_state_frac: ps,
                inv: i.clone(),
                credit: credit.get(),
            })
        }
    }

    // Flushing to ensure that the inactive range is prepared to be made active.
    pub struct PreparingFlush<'a> {
        pub ptr_state_frac: Frac<PtrState>,
        pub preparing_frac: &'a SeqFrac<u8>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        pub credit: OpenInvariantCredit,
    }

    impl<'a> ReadLinearizer<FlushOp> for PreparingFlush<'a> {
        type ApplyResult = Frac<PtrState>;

        closed spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: FlushOp) -> bool {
            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& self.preparing_frac.valid(op.id)
            &&& self.preparing_frac@[0] + self.preparing_frac@[1] == total
            &&& op.persist_id == self.inv.constant().persist_id
            &&& self.preparing_frac@.len() == 2
            &&& {
                ||| {
                    &&& self.preparing_frac.off() == a_addr
                    &&& self.ptr_state_frac@ == PtrState::B
                    }
                ||| {
                    &&& self.preparing_frac.off() == b_addr
                    &&& self.ptr_state_frac@ == PtrState::A
                    }
                }
        }

        open spec fn post(self, op: FlushOp, r: (), ar: Frac<PtrState>) -> bool {
            &&& ar.valid(self.inv.constant().ptr_state_id, 1)
            &&& ar@ == PtrState::Either
        }

        proof fn apply(tracked self, op: FlushOp, tracked r: &DiskResources, e: &()) -> (tracked result: Frac<PtrState>) {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                mself.ptr_state_frac.combine(inner.ptr_state);
                mself.preparing_frac.agree(&r.latest);
                inner.a.agree(&r.persist);
                inner.b.agree(&r.persist);
                mself.ptr_state_frac.update(PtrState::Either);
                inner.ptr_state = mself.ptr_state_frac.split(1);
            });
            mself.ptr_state_frac
        }

        proof fn peek(tracked &self, op: FlushOp, tracked r: &DiskResources) {}
    }

    impl<'a> PreparingFlush<'a> {
        pub fn new(Tracked(ps): Tracked<Frac<PtrState>>, Tracked(pf): Tracked<&'a SeqFrac<u8>>, Tracked(i): Tracked<&Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>>) -> (result: Tracked<Self>)
            ensures
                result@.ptr_state_frac == ps,
                result@.preparing_frac == pf,
                result@.inv == i,
        {
            let credit = create_open_invariant_credit();
            Tracked(Self{
                ptr_state_frac: ps,
                preparing_frac: pf,
                inv: i.clone(),
                credit: credit.get(),
            })
        }
    }

    // Flipping the pointer.
    pub struct CommittingWriter {
        pub latest_frac: SeqFrac<u8>,
        pub ptr_state_frac: Frac<PtrState>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        pub credit: OpenInvariantCredit,
    }

    impl MutLinearizer<WriteOp> for CommittingWriter {
        type ApplyResult = (SeqFrac<u8>, Frac<PtrState>);

        closed spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: WriteOp) -> bool {
            &&& self.latest_frac.valid(op.id)
            &&& self.latest_frac.off() <= op.addr
            &&& op.addr + op.data.len() <= self.latest_frac.off() + self.latest_frac@.len()

            &&& op.persist_id == self.inv.constant().persist_id
            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& self.ptr_state_frac@ == PtrState::Either
            &&& op.addr == ptr_addr
            &&& (op.data =~= seq![0u8] || op.data =~= seq![1u8])
        }

        open spec fn post(self, op: WriteOp, r: (), ar: Self::ApplyResult) -> bool {
            &&& ar.0.valid(op.id)
            &&& ar.0.off() == self.latest_frac.off()
            &&& ar.0@ == update_seq(self.latest_frac@, op.addr - self.latest_frac.off(), op.data)

            &&& ar.1.valid(self.inv.constant().ptr_state_id, 1)
            &&& ar.1@ == PtrState::Either
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut DiskResources, e: &()) -> (tracked result: Self::ApplyResult) {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                mself.ptr_state_frac.agree(&inner.ptr_state);
                inner.ptr.agree(&r.persist);
                inner.ptr.update(&mut r.persist, pstate);
            });

            mself.latest_frac.agree(&r.latest);
            mself.latest_frac.update_range(&mut r.latest, op.addr - mself.latest_frac.off(), op.data);

            (mself.latest_frac, mself.ptr_state_frac)
        }

        proof fn peek(tracked &self, op: WriteOp, tracked r: &DiskResources) {
            self.latest_frac.agree(&r.latest);
        }
    }

    impl CommittingWriter {
        pub fn new(Tracked(lf): Tracked<SeqFrac<u8>>, Tracked(ps): Tracked<Frac<PtrState>>,
               Tracked(i): Tracked<&Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>>) -> (result: Tracked<Self>)
            ensures
                result@.latest_frac == lf,
                result@.ptr_state_frac == ps,
                result@.inv == i,
        {
            let credit = create_open_invariant_credit();
            Tracked(Self{
                latest_frac: lf,
                ptr_state_frac: ps,
                inv: i.clone(),
                credit: credit.get(),
            })
        }
    }

    // Flushing after a pointer update.
    pub struct CommittingFlush<'a> {
        pub ptr_state_frac: Frac<PtrState>,
        pub ptr_latest: &'a SeqFrac<u8>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        pub credit: OpenInvariantCredit,
    }

    impl<'a> ReadLinearizer<FlushOp> for CommittingFlush<'a> {
        type ApplyResult = Frac<PtrState>;

        closed spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: FlushOp) -> bool {
            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& self.ptr_latest.valid(op.id)
            &&& self.inv.constant().persist_id == op.persist_id
            &&& self.ptr_latest.off() == ptr_addr
            &&& self.ptr_latest@.len() == 1
        }

        open spec fn post(self, op: FlushOp, r: (), ar: Frac<PtrState>) -> bool {
            &&& ar.valid(self.inv.constant().ptr_state_id, 1)
            &&& {
                ||| self.ptr_latest@[0] == 0 && ar@ == PtrState::A
                ||| self.ptr_latest@[0] == 1 && ar@ == PtrState::B
                }
        }

        proof fn apply(tracked self, op: FlushOp, tracked r: &DiskResources, e: &()) -> (tracked result: Frac<PtrState>) {
            let tracked mut mself = self;
            mself.ptr_latest.agree(&r.latest);
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                inner.ptr.agree(&r.persist);

                mself.ptr_state_frac.combine(inner.ptr_state);
                if self.ptr_latest@[0] == 0 {
                    mself.ptr_state_frac.update(PtrState::A);
                } else {
                    mself.ptr_state_frac.update(PtrState::B);
                }
                inner.ptr_state = mself.ptr_state_frac.split(1);
            });
            mself.ptr_state_frac
        }

        proof fn peek(tracked &self, op: FlushOp, tracked r: &DiskResources) {}
    }

    impl<'a> CommittingFlush<'a> {
        pub fn new(Tracked(ps): Tracked<Frac<PtrState>>, Tracked(pl): Tracked<&'a SeqFrac<u8>>, Tracked(i): Tracked<&Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>>) -> (result: Tracked<Self>)
            ensures
                result@.ptr_state_frac == ps,
                result@.ptr_latest == pl,
                result@.inv == i,
        {
            let credit = create_open_invariant_credit();
            Tracked(Self{
                ptr_state_frac: ps,
                ptr_latest: pl,
                inv: i.clone(),
                credit: credit.get(),
            })
        }
    }
}
