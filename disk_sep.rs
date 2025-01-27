mod disk;

use std::sync::Arc;

use disk::vecdisk::*;
use disk::disk_wrap::*;
use disk::logatom::*;
use disk::seq_view::*;
use disk::frac::*;

use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    const ptr_addr: usize = 0;
    const a_addr: usize = 1;
    const b_addr: usize = 3;
    const total: u8 = 10;

    enum PtrState {
        A,
        B,
        Either,
    }

    struct DiskCrashState {
        ptr: SeqFrac<u8>,
        a: SeqFrac<u8>,
        b: SeqFrac<u8>,
        ptr_state: Frac<PtrState>,
    }

    struct DiskInvParam {
        persist_id: int,
        ptr_state_id: int,
    }

    impl InvariantPredicate<DiskInvParam, DiskCrashState> for DiskInvParam {
        closed spec fn inv(k: DiskInvParam, inner: DiskCrashState) -> bool {
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

    // Writing to an address where we fully own the crash resource.
    struct OwningWriter {
        frac: SeqFrac<u8>,
    }

    impl MutLinearizer<WriteOp> for OwningWriter {
        type ApplyResult = SeqFrac<u8>;

        closed spec fn pre(self, op: WriteOp) -> bool {
            &&& self.frac.valid(op.persist_id)
            &&& self.frac.off() == op.addr
            &&& self.frac@.len() == op.data.len()
        }

        closed spec fn post(self, op: WriteOp, r: (), ar: SeqFrac<u8>) -> bool {
            &&& ar.valid(op.persist_id)
            &&& ar.off() == op.addr
            &&& can_result_from_write(ar@, self.frac@, 0, op.data)
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut SeqAuth<u8>, e: &()) -> (tracked out: SeqFrac<u8>) {
            let tracked mut mself = self;
            mself.frac.agree(r);
            mself.frac.update(r, pstate);
            mself.frac
        }
    }

    // Flushing to learn that a particular range is now consistently on-disk.
    struct OwningFlush<'a> {
        latest_frac: &'a SeqFrac<u8>,
        persist_frac: &'a SeqFrac<u8>,
    }

    impl<'a> ReadLinearizer<FlushOp> for OwningFlush<'a> {
        type ApplyResult = ();

        closed spec fn pre(self, op: FlushOp) -> bool {
            &&& self.latest_frac.valid(op.id)
            &&& self.persist_frac.valid(op.persist_id)
            &&& self.latest_frac.off() == self.persist_frac.off()
            &&& self.latest_frac@.len() == self.persist_frac@.len()
        }

        closed spec fn post(self, op: FlushOp, r: (), ar: ()) -> bool {
            &&& self.latest_frac@ == self.persist_frac@
        }

        proof fn apply(tracked self, op: FlushOp, tracked r: &DiskResources, e: &()) -> (tracked result: ()) {
            self.latest_frac.agree(&r.latest);
            self.persist_frac.agree(&r.persist);
        }
    }

    // Writing to a block that's currently unused.
    struct InactiveWriter<'a> {
        ptr_state_frac: &'a Frac<PtrState>,
        inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        credit: OpenInvariantCredit,
    }

    impl<'a> MutLinearizer<WriteOp> for InactiveWriter<'a> {
        type ApplyResult = ();

        closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        closed spec fn pre(self, op: WriteOp) -> bool {
            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& op.persist_id == self.inv.constant().persist_id
            &&& op.data.len() == 2
            &&& {
                ||| op.addr == a_addr && self.ptr_state_frac@ == PtrState::B
                ||| op.addr == b_addr && self.ptr_state_frac@ == PtrState::A
                }
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut SeqAuth<u8>, e: &()) {
            let tracked mut mself = self;
            open_atomic_invariant!(mself.credit => &mself.inv => inner => {
                mself.ptr_state_frac.agree(&inner.ptr_state);

                if op.addr == a_addr {
                    inner.a.agree(r);
                    inner.a.update(r, pstate);
                } else {
                    inner.b.agree(r);
                    inner.b.update(r, pstate);
                }
            });
        }
    }

    impl<'a> InactiveWriter<'a> {
        fn new(Tracked(ps): Tracked<&'a Frac<PtrState>>, Tracked(i): Tracked<&Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>>) -> (result: Tracked<Self>)
            ensures
                result@.ptr_state_frac == ps,
                result@.inv == i,
        {
            let credit = create_open_invariant_credit();
            Tracked(Self{
                ptr_state_frac: ps,
                inv: i.clone(),
                credit: credit.get(),
            })
        }
    }

    // Flushing to ensure that the inactive range is prepared to be made active.
    struct PreparingFlush<'a> {
        ptr_state_frac: Frac<PtrState>,
        preparing_frac: &'a SeqFrac<u8>,
        inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        credit: OpenInvariantCredit,
    }

    impl<'a> ReadLinearizer<FlushOp> for PreparingFlush<'a> {
        type ApplyResult = Frac<PtrState>;

        closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        closed spec fn pre(self, op: FlushOp) -> bool {
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

        closed spec fn post(self, op: FlushOp, r: (), ar: Frac<PtrState>) -> bool {
            &&& ar.valid(self.inv.constant().ptr_state_id, 1)
            &&& ar@ == PtrState::Either
        }

        proof fn apply(tracked self, op: FlushOp, tracked r: &DiskResources, e: &()) -> (tracked result: Frac<PtrState>) {
            let tracked mut mself = self;
            open_atomic_invariant!(mself.credit => &mself.inv => inner => {
                mself.ptr_state_frac.combine(inner.ptr_state);
                mself.preparing_frac.agree(&r.latest);
                inner.a.agree(&r.persist);
                inner.b.agree(&r.persist);
                mself.ptr_state_frac.update(PtrState::Either);
                inner.ptr_state = mself.ptr_state_frac.split(1);
            });
            mself.ptr_state_frac
        }
    }

    impl<'a> PreparingFlush<'a> {
        fn new(Tracked(ps): Tracked<Frac<PtrState>>, Tracked(pf): Tracked<&'a SeqFrac<u8>>, Tracked(i): Tracked<&Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>>) -> (result: Tracked<Self>)
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
    struct CommittingWriter {
        ptr_state_frac: Frac<PtrState>,
        inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        credit: OpenInvariantCredit,
    }

    impl MutLinearizer<WriteOp> for CommittingWriter {
        type ApplyResult = Frac<PtrState>;

        closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        closed spec fn pre(self, op: WriteOp) -> bool {
            &&& op.persist_id == self.inv.constant().persist_id
            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& self.ptr_state_frac@ == PtrState::Either
            &&& op.addr == ptr_addr
            &&& (op.data =~= seq![0u8] || op.data =~= seq![1u8])
        }

        closed spec fn post(self, op: WriteOp, r: (), ar: Frac<PtrState>) -> bool {
            &&& ar.valid(self.inv.constant().ptr_state_id, 1)
            &&& ar@ == PtrState::Either
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut SeqAuth<u8>, e: &()) -> (tracked result: Frac<PtrState>) {
            let tracked mut mself = self;
            open_atomic_invariant!(mself.credit => &mself.inv => inner => {
                mself.ptr_state_frac.agree(&inner.ptr_state);
                inner.ptr.agree(r);
                inner.ptr.update(r, pstate);
            });
            mself.ptr_state_frac
        }
    }

    // Flushing after a pointer update.
    struct CommittingFlush<'a> {
        ptr_state_frac: Frac<PtrState>,
        ptr_latest: &'a SeqFrac<u8>,
        inv: Arc<AtomicInvariant<DiskInvParam, DiskCrashState, DiskInvParam>>,
        credit: OpenInvariantCredit,
    }

    impl<'a> ReadLinearizer<FlushOp> for CommittingFlush<'a> {
        type ApplyResult = Frac<PtrState>;

        closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        closed spec fn pre(self, op: FlushOp) -> bool {
            &&& self.ptr_state_frac.valid(self.inv.constant().ptr_state_id, 1)
            &&& self.ptr_latest.valid(op.id)
            &&& self.inv.constant().persist_id == op.persist_id
            &&& self.ptr_latest.off() == ptr_addr
        }

        closed spec fn post(self, op: FlushOp, r: (), ar: Frac<PtrState>) -> bool {
            &&& ar.valid(self.inv.constant().ptr_state_id, 1)
            &&& {
                ||| self.ptr_latest@[0] == 0 && ar@ == PtrState::A
                ||| self.ptr_latest@[0] == 1 && ar@ == PtrState::B
                }
        }

        proof fn apply(tracked self, op: FlushOp, tracked r: &DiskResources, e: &()) -> (tracked result: Frac<PtrState>) {
            let tracked mut mself = self;
            mself.ptr_latest.agree(&r.latest);
            open_atomic_invariant!(mself.credit => &mself.inv => inner => {
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
    }

    // Test of separation-logic interface with invariant ownership of crash (persist) resources.
    //
    // test_inv_init() sets up the disk and allocates the invariant for the first time, like mkfs.
    //
    // test_inv_recover() recovers from a crash on a disk that already was initialized.
    fn test_inv_init() {
        let d = Disk::new(5);
        let (mut dw, Tracked(mut f), Tracked(mut pf)) = DiskWrap::new(d);

        let Tracked(mut pf) = dw.write::<OwningWriter>(0, &[0, 5, 5, 3, 7], Tracked(&mut f), Tracked(OwningWriter{ frac: pf }));
        dw.flush::<OwningFlush>(Tracked(OwningFlush{ latest_frac: &f, persist_frac: &pf }));

        let tracked mut f1 = f.split(1);
        let tracked mut pf1 = pf.split(1);

        let tracked mut f3 = f1.split(2);
        let tracked mut pf3 = pf1.split(2);

        let tracked mut ps = Frac::new(PtrState::A);

        let tracked crashstate = DiskCrashState{
            ptr: pf,
            a: pf1,
            b: pf3,
            ptr_state: ps.split(1),
        };

        let ghost iparam = DiskInvParam{
            persist_id: pf.id(),
            ptr_state_id: ps.id(),
        };

        let tracked i = AtomicInvariant::<_, _, DiskInvParam>::new(iparam, crashstate, 12345);
        let tracked i = Arc::new(i);

        // Help instantiate triggers later.
        assert(dw.persist_id() == i.constant().persist_id);

        // Write new data to area B; allowed because it's not the active area.
        dw.write(3, &[1, 9], Tracked(&mut f3), InactiveWriter::new(Tracked(&ps), Tracked(&i)));

        // Flush the new data in area B so it's ready to commit.
        let Tracked(ps) = dw.flush(PreparingFlush::new(Tracked(ps), Tracked(&f3), Tracked(&i)));

        // Flip the pointer: either area A or B could be there on crash, and either is valid.
        let credit = create_open_invariant_credit();
        let Tracked(ps) = dw.write::<CommittingWriter>(0, &[1], Tracked(&mut f), Tracked(CommittingWriter{ ptr_state_frac: ps, inv: i.clone(), credit: credit.get() }));
        assert(ps@ == PtrState::Either);

        // Flush the pointer, so we know it's definitely area B that's durable now.
        let credit = create_open_invariant_credit();
        let Tracked(ps) = dw.flush::<CommittingFlush>(Tracked(CommittingFlush{ ptr_state_frac: ps, ptr_latest: &f, inv: i.clone(), credit: credit.get() }));
        assert(ps@ == PtrState::B);

        // Temporarily write bogus data to area A, but it doesn't matter because it's not active.
        // Then write valid data.
        dw.write(1, &[0, 0], Tracked(&mut f1), InactiveWriter::new(Tracked(&ps), Tracked(&i)));
        dw.write(1, &[2, 8], Tracked(&mut f1), InactiveWriter::new(Tracked(&ps), Tracked(&i)));

        // Flush the new contents of area A before commit.
        let Tracked(ps) = dw.flush(PreparingFlush::new(Tracked(ps), Tracked(&f1), Tracked(&i)));

        // Write and commit the pointer, switching back to area A.
        let credit = create_open_invariant_credit();
        let Tracked(ps) = dw.write::<CommittingWriter>(0, &[0], Tracked(&mut f), Tracked(CommittingWriter{ ptr_state_frac: ps, inv: i.clone(), credit: credit.get() }));
        assert(ps@ == PtrState::Either);

        let credit = create_open_invariant_credit();
        let Tracked(ps) = dw.flush::<CommittingFlush>(Tracked(CommittingFlush{ ptr_state_frac: ps, ptr_latest: &f, inv: i.clone(), credit: credit.get() }));
        assert(ps@ == PtrState::A);
    }

    // CORE ASSUMPTION: the disk contains state that satisfied our invariant before crash.
    #[verifier::external_body]
    proof fn disk_recovery_axiom_helper(tracked pf: SeqFrac<u8>) -> (tracked result: AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>)
        requires
            // Not a complete set of preconditions for soundness; requires trusting caller too.
            pf.inv(),
            pf.off() == 0,
            pf@.len() >= 5,
        ensures
            // Core postcondition: the invariant talks about contents of the recovered disk!
            result.constant().persist_id == pf.id(),
    {
        unimplemented!();
    }

    // CORE ASSUMPTION: we can get a disk object and an invariant that talks about that disk's
    // persistent state.
    fn disk_recovery_axiom() -> (result: (DiskWrap, Tracked<SeqFrac<u8>>, Tracked<AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>>))
        ensures
            result.0.inv(),
            result.1@.valid(result.0.id()),
            result.1@.off() == 0,
            result.1@@.len() == 5,
            result.2@.constant().persist_id == result.0.persist_id(),
    {
        let d = Disk::new(5);
        let (dw, Tracked(mut f), Tracked(mut pf)) = DiskWrap::new(d);
        let tracked i = disk_recovery_axiom_helper(pf);
        (dw, Tracked(f), Tracked(i))
    }

    // Untrusted (verified) recovery helper: re-allocate ephemeral ghost state.
    fn disk_recovery_verified_helper(Tracked(i): Tracked<AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>>) -> (result: (Tracked<AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>>, Tracked<Frac<PtrState>>))
        ensures
            result.1@.valid(result.0@.constant().ptr_state_id, 1),
            result.0@.constant().persist_id == i.constant().persist_id,
    {
        // Destroy the invariant; we will re-allocate a new one with a different ptr_state_id.
        let ghost mut iparam = i.constant();
        let tracked inner = i.into_inner();

        let tracked mut ps = Frac::new(inner.ptr_state@);
        proof {
            inner.ptr_state = ps.split(1);
            iparam.ptr_state_id = ps.id();
        }

        // Allocate a new invariant.
        let tracked i = AtomicInvariant::<_, _, DiskInvParam>::new(iparam, inner, i.namespace());

        (Tracked(i), Tracked(ps))
    }

    fn test_inv_recover() {
        let (mut dw, Tracked(mut f), Tracked(i)) = disk_recovery_axiom();

        // Re-allocate ptr_state_frac.
        let (Tracked(i), Tracked(mut ps)) = disk_recovery_verified_helper(Tracked(i));
        let tracked i = Arc::new(i);

        let tracked mut f1 = f.split(1);
        let tracked mut f3 = f1.split(2);

        // Superfluous flush: establish that ps@ is either A or B.
        // Really, we should know that f@ == pf@ (persistent state).
        let credit = create_open_invariant_credit();
        let Tracked(ps) = dw.flush::<CommittingFlush>(Tracked(CommittingFlush{ ptr_state_frac: ps, ptr_latest: &f, inv: i.clone(), credit: credit.get() }));
        assert(ps@ == PtrState::A || ps@ == PtrState::B);

        let ptr = dw.read(0, 1, Tracked(&f));
        if ptr[0] == 0 {
            assert(ps@ == PtrState::A);
        } else {
            assert(ps@ == PtrState::B);

            // Temporarily write bogus data to area A, but it doesn't matter because it's not active.
            // Then write valid data.
            dw.write(1, &[0, 0], Tracked(&mut f1), InactiveWriter::new(Tracked(&ps), Tracked(&i)));
            dw.write(1, &[2, 8], Tracked(&mut f1), InactiveWriter::new(Tracked(&ps), Tracked(&i)));

            // Flush the new contents of area A before commit.
            let Tracked(ps) = dw.flush(PreparingFlush::new(Tracked(ps), Tracked(&f1), Tracked(&i)));

            // Write and commit the pointer, switching back to area A.
            let credit = create_open_invariant_credit();
            let Tracked(ps) = dw.write::<CommittingWriter>(0, &[0], Tracked(&mut f), Tracked(CommittingWriter{ ptr_state_frac: ps, inv: i.clone(), credit: credit.get() }));
            assert(ps@ == PtrState::Either);

            let credit = create_open_invariant_credit();
            let Tracked(ps) = dw.flush::<CommittingFlush>(Tracked(CommittingFlush{ ptr_state_frac: ps, ptr_latest: &f, inv: i.clone(), credit: credit.get() }));
            assert(ps@ == PtrState::A);
        }
    }

    // Lower-level test of writing to disk addresses with full ownership of crash resources.
    fn test_rw() {
        let d = Disk::new(1024);
        let (mut dw, Tracked(mut f0), Tracked(mut pf0)) = DiskWrap::new(d);

        let tracked mut f4 = f0.split(4);
        let tracked mut f8 = f4.split(4);

        let tracked mut pf4 = pf0.split(4);
        let tracked mut pf8 = pf4.split(4);

        assert(f0@ == seq![0u8, 0u8, 0u8, 0u8]);

        let Tracked(pf0) = dw.write::<OwningWriter>(0, &[120, 121, 122, 123], Tracked(&mut f0), Tracked(OwningWriter{ frac: pf0 }));
        let Tracked(pf4) = dw.write::<OwningWriter>(4, &[124, 125, 126, 127], Tracked(&mut f4), Tracked(OwningWriter{ frac: pf4 }));

        assert(f0@ == seq![120u8, 121u8, 122u8, 123u8]);

        let x = dw.read(0, 4, Tracked(&f0));
        assert(x@ == seq![120u8, 121u8, 122u8, 123u8]);
        let x = dw.read(4, 4, Tracked(&f4));
        assert(x@ == seq![124u8, 125u8, 126u8, 127u8]);
    }

    fn main() {
        test_rw();
        test_inv_init();
    }
}
