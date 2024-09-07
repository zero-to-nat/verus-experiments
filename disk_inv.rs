use builtin::*;
use vstd::prelude::*;
use vstd::invariant::*;
use std::sync::Arc;

mod disk;

use frac::FractionalResource;

use disk::DiskView;
use disk::MemCrashView;
use disk::view_read;
use disk::view_write;
use disk::frac;
use disk::Disk;
use disk::DiskReadPermission;
use disk::DiskWritePermission;
use disk::DiskBarrierPermission;
use disk::DISK_INV_NS;

verus! {
    pub type AbsView = u8;

    pub open spec fn abs_inv(abs: AbsView, disk: DiskView) -> bool
    {
        abs == disk.0 && disk.0 <= disk.1
    }

    pub struct AbsPair {
        pub mem: AbsView,
        pub crash: AbsView,
    }

    pub struct DiskInvState {
        // Actual disk state.
        disk: FractionalResource<MemCrashView, 2>,

        // Re-exporting disk state for applicaton to track intermediate writes.
        disk2: FractionalResource<MemCrashView, 2>,

        // Abstract state (memory and crash).
        abs: FractionalResource<AbsPair, 2>,
    }

    pub struct DiskInvParam {
        pub disk_id: int,
        pub disk2_id: int,
        pub abs_id: int,
    }

    pub struct DiskInvPred {}

    impl InvariantPredicate<DiskInvParam, DiskInvState> for DiskInvPred
    {
        closed spec fn inv(k: DiskInvParam, v: DiskInvState) -> bool {
            v.disk.valid(k.disk_id, 1) &&
            v.disk2.valid(k.disk2_id, 1) &&
            v.abs.valid(k.abs_id, 1) &&
            v.disk.val() == v.disk2.val() &&
            abs_inv(v.abs.val().mem, v.disk.val().mem) &&
            abs_inv(v.abs.val().crash, v.disk.val().crash)
        }
    }

    pub struct InvPermResult
    {
        pub disk2_frac: FractionalResource<MemCrashView, 2>,
        pub app_frac: FractionalResource<AbsPair, 2>,
    }

    pub struct InvWritePerm
    {
        pub a: u8,
        pub v: u8,
        pub tracked disk2_frac: FractionalResource<MemCrashView, 2>,
        pub tracked app_frac: FractionalResource<AbsPair, 2>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
    }

    impl DiskWritePermission<InvPermResult> for InvWritePerm
    {
        open spec fn id(&self) -> int { self.inv.constant().disk_id }
        open spec fn addr(&self) -> u8 { self.a }
        open spec fn val(&self) -> u8 { self.v }

        open spec fn pre(&self) -> bool {
            self.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            self.app_frac.valid(self.inv.constant().abs_id, 1) &&

            self.inv.namespace() == DISK_INV_NS &&

            if self.addr() == 0 {
                self.val() <= self.disk2_frac.val().mem.1 &&
                self.val() <= self.disk2_frac.val().crash.1
            } else {
                self.val() >= self.disk2_frac.val().mem.0 &&
                self.val() >= self.disk2_frac.val().crash.0
            }
        }

        open spec fn post(&self, r: InvPermResult) -> bool {
            r.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            r.disk2_frac.val().mem == view_write(self.disk2_frac.val().mem, self.addr(), self.val()) &&
            ( r.disk2_frac.val().crash == self.disk2_frac.val().crash ||
              r.disk2_frac.val().crash == view_write(self.disk2_frac.val().crash, self.addr(), self.val()) ) &&

            r.app_frac.valid(self.inv.constant().abs_id, 1) &&
            r.app_frac.val().mem == if self.addr() == 0 { self.val() } else { self.app_frac.val().mem } &&
            ( r.app_frac.val().crash == self.app_frac.val().crash ||
              ( self.addr() == 0 && r.app_frac.val().crash == self.val() ) )
        }

        proof fn apply(tracked self, tracked mut r: FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: (FractionalResource<MemCrashView, 2>, InvPermResult))
        {
            let tracked mut mself = self;
            let tracked mut ires: Option<InvPermResult> = None;
            open_atomic_invariant!(credit => &mself.inv => inner => {
                r.combine_mut(inner.disk);
                r.update_mut(MemCrashView{
                        mem: view_write(r.val().mem, mself.addr(), mself.val()),
                        crash: if write_crash { view_write(r.val().crash, mself.addr(), mself.val()) } else { r.val().crash },
                    });
                inner.disk = r.split_mut(1);

                mself.disk2_frac.combine_mut(inner.disk2);
                mself.disk2_frac.update_mut(inner.disk.val());
                inner.disk2 = mself.disk2_frac.split_mut(1);

                if mself.addr() == 0 {
                    mself.app_frac.combine_mut(inner.abs);
                    mself.app_frac.update_mut(AbsPair{
                        mem: mself.val(),
                        crash: if write_crash { mself.val() } else { mself.app_frac.val().crash },
                    });
                    inner.abs = mself.app_frac.split_mut(1)
                };

                ires = Some(InvPermResult{
                    disk2_frac: mself.disk2_frac,
                    app_frac: mself.app_frac,
                })
            });

            (r, ires.tracked_unwrap())
        }
    }

    pub struct InvBarrierPerm
    {
        pub tracked disk2_frac: FractionalResource<MemCrashView, 2>,
        pub tracked app_frac: FractionalResource<AbsPair, 2>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
    }

    impl DiskBarrierPermission<InvPermResult> for InvBarrierPerm
    {
        open spec fn id(&self) -> int { self.inv.constant().disk_id }

        open spec fn pre(&self) -> bool {
            self.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            self.app_frac.valid(self.inv.constant().abs_id, 1) &&

            self.inv.namespace() == DISK_INV_NS
        }

        open spec fn post(&self, r: InvPermResult) -> bool {
            r.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            r.app_frac.valid(self.inv.constant().abs_id, 1) &&

            r.disk2_frac.val() == self.disk2_frac.val() &&
            r.disk2_frac.val().mem == r.disk2_frac.val().crash &&

            r.app_frac.val() == self.app_frac.val() &&
            r.app_frac.val().mem == r.app_frac.val().crash
        }

        proof fn apply(tracked self, tracked mut r: FractionalResource<MemCrashView, 2>, tracked credit: OpenInvariantCredit) -> (tracked result: (FractionalResource<MemCrashView, 2>, InvPermResult))
        {
            let tracked mut mself = self;
            open_atomic_invariant!(credit => &mself.inv => inner => {
                r.agree(&inner.disk);
                mself.disk2_frac.agree(&inner.disk2);
                mself.app_frac.agree(&inner.abs);
            });

            (r, InvPermResult{
                disk2_frac: mself.disk2_frac,
                app_frac: mself.app_frac,
            })
        }
    }

    pub struct InvReadPerm
    {
        pub a: u8,
        pub tracked disk2_frac: FractionalResource<MemCrashView, 2>,
        pub tracked app_frac: FractionalResource<AbsPair, 2>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
    }

    impl DiskReadPermission<InvPermResult> for InvReadPerm
    {
        open spec fn id(&self) -> int { self.inv.constant().disk_id }
        open spec fn addr(&self) -> u8 { self.a }

        open spec fn pre(&self) -> bool {
            self.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            self.app_frac.valid(self.inv.constant().abs_id, 1) &&
            self.inv.namespace() == DISK_INV_NS
        }

        open spec fn post(&self, r: InvPermResult, v: u8) -> bool {
            r.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            r.app_frac.valid(self.inv.constant().abs_id, 1) &&

            r.disk2_frac.val() == self.disk2_frac.val() &&
            r.app_frac.val() == self.app_frac.val() &&

            v == view_read(r.disk2_frac.val().mem, self.addr())
        }

        proof fn apply(tracked self, tracked mut r: FractionalResource<MemCrashView, 2>, v: u8, tracked credit: OpenInvariantCredit) -> (tracked result: (FractionalResource<MemCrashView, 2>, InvPermResult))
        {
            let tracked mut mself = self;
            open_atomic_invariant!(credit => &mself.inv => inner => {
                r.agree(&inner.disk);
                mself.disk2_frac.agree(&inner.disk2);
                mself.app_frac.agree(&inner.abs);
            });

            (r, InvPermResult{
                disk2_frac: mself.disk2_frac,
                app_frac: mself.app_frac,
            })
        }
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::alloc();

        let tracked app_r = FractionalResource::<AbsPair, 2>::alloc(AbsPair{ mem: 0, crash: 0 });
        let tracked (app_r, app_r1) = app_r.split(1);

        let tracked disk_r = FractionalResource::<MemCrashView, 2>::alloc(r.val());
        let tracked (disk_r, disk_r1) = disk_r.split(1);

        let ghost inv_param = DiskInvParam{
            disk_id: r.id(),
            disk2_id: disk_r1.id(),
            abs_id: app_r1.id(),
        };

        let tracked inv_st = DiskInvState{
            disk: r,
            disk2: disk_r1,
            abs: app_r1,
        };

        let tracked i = AtomicInvariant::<_, _, DiskInvPred>::new(inv_param, inv_st, disk::DISK_INV_NS as int);
        let tracked i = Arc::new(i);

        let tracked fupd = InvReadPerm{ a: 0u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let (x0, Tracked(res)) = d.read::<_, InvReadPerm>(0, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let tracked fupd = InvReadPerm{ a: 1u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let (x1, Tracked(res)) = d.read::<_, InvReadPerm>(1, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        assert(x0 == 0 && x1 == 0);

        let tracked fupd = InvWritePerm{ a: 1u8, v: 5u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let Tracked(res) = d.write::<_, InvWritePerm>(1, 5, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let tracked fupd = InvReadPerm{ a: 0u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let (x0, Tracked(res)) = d.read::<_, InvReadPerm>(0, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let tracked fupd = InvReadPerm{ a: 1u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let (x1, Tracked(res)) = d.read::<_, InvReadPerm>(1, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        assert(x0 == 0 && x1 == 5);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        let tracked fupd = InvBarrierPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let Tracked(res) = d.barrier::<_, InvBarrierPerm>(Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let tracked fupd = InvWritePerm{ a: 0u8, v: 2u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let Tracked(res) = d.write::<_, InvWritePerm>(0, 2, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let tracked fupd = InvReadPerm{ a: 0u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let (x0, Tracked(res)) = d.read::<_, InvReadPerm>(0, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let tracked fupd = InvReadPerm{ a: 1u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone() };
        let (x1, Tracked(res)) = d.read::<_, InvReadPerm>(1, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        assert(x0 == 2 && x1 == 5);

        ()
    }
}
