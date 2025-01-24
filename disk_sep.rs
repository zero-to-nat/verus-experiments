mod disk;

use disk::vecdisk::*;
use disk::disk_wrap::*;
use disk::logatom::*;
use disk::seq_view::*;
use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    struct DiskCrashState {
        ptr: SeqFrac<u8>,
        a: SeqFrac<u8>,
        b: SeqFrac<u8>,
    }

    struct DiskInvParam {
        persist_id: int,
        ptr_addr: usize,
        a_addr: usize,
        b_addr: usize,
        total: int,
    }

    impl InvariantPredicate<DiskInvParam, DiskCrashState> for DiskInvParam {
        closed spec fn inv(k: DiskInvParam, v: DiskCrashState) -> bool {
            &&& v.ptr.valid(k.persist_id)
            &&& v.ptr.off() == k.ptr_addr
            &&& v.ptr@.len() == 1

            &&& v.a.valid(k.persist_id)
            &&& v.a.off() == k.a_addr
            &&& v.a@.len() == 2

            &&& v.b.valid(k.persist_id)
            &&& v.b.off() == k.b_addr
            &&& v.b@.len() == 2

            &&& if v.ptr@[0] == 0 {
                    v.a@[0] + v.a@[1] == k.total
                } else {
                    v.b@[0] + v.b@[1] == k.total
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

    // Test of separation-logic interface with invariant ownership of crash (persist) resources.
    fn test_inv() {
        let d = Disk::new(5);
        let (mut dw, Tracked(mut f), Tracked(mut pf)) = DiskWrap::new(d);

        let Tracked(mut pf) = dw.write::<OwningWriter>(0, &[0, 5, 5, 3, 7], Tracked(&mut f), Tracked(OwningWriter{ frac: pf }));
        dw.flush::<OwningFlush>(Tracked(OwningFlush{ latest_frac: &f, persist_frac: &pf }));

        let tracked mut f1 = f.split(1);
        let tracked mut pf1 = pf.split(1);

        let tracked mut f3 = f1.split(2);
        let tracked mut pf3 = pf1.split(2);

        let tracked crashstate = DiskCrashState{
            ptr: pf,
            a: pf1,
            b: pf3,
        };

        let ghost iparam = DiskInvParam{
            persist_id: pf.id(),
            ptr_addr: 0,
            a_addr: 1,
            b_addr: 3,
            total: 10,
        };

        let tracked i = AtomicInvariant::<_, _, DiskInvParam>::new(iparam, crashstate, 12345);

        
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
        test_inv();
    }
}
