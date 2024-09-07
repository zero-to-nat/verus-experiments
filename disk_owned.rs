use builtin::*;
use vstd::prelude::*;
use vstd::invariant::*;

mod disk;

use disk::DiskView;
use disk::MemCrashView;
use disk::view_write;
use disk::frac;
use frac::FractionalResource;
use disk::Disk;
use disk::DiskWritePermission;

verus! {
    pub type AbsView = u8;

    pub open spec fn abs_inv(abs: AbsView, disk: DiskView) -> bool
    {
        abs == disk.0 && disk.0 <= disk.1
    }

    pub struct WriteFupd
    {
        pub a: u8,
        pub v: u8,
        pub tracked frac: FractionalResource<MemCrashView, 2>,
        pub ghost abs_pre: AbsView,
        pub ghost abs_post: AbsView,
    }

    impl DiskWritePermission<FractionalResource<MemCrashView, 2>> for WriteFupd
    {
        open spec fn id(&self) -> int { self.frac.id() }
        open spec fn addr(&self) -> u8 { self.a }
        open spec fn val(&self) -> u8 { self.v }

        open spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.frac.frac() == 1 &&
            if self.addr() == 0 {
                self.abs_post == self.val() &&
                self.val() <= self.frac.val().mem.1 &&
                self.val() <= self.frac.val().crash.1
            } else {
                self.abs_post == self.abs_pre &&
                self.val() >= self.abs_pre
            } &&
            abs_inv(self.abs_pre, self.frac.val().mem) &&
            abs_inv(self.abs_pre, self.frac.val().crash)
        }

        open spec fn post(&self, r: FractionalResource<MemCrashView, 2>) -> bool {
            r.valid(self.id(), 1) &&
            r.val().mem == view_write(self.frac.val().mem, self.addr(), self.val()) &&
            ( r.val().crash == self.frac.val().crash ||
              r.val().crash == view_write(self.frac.val().crash, self.addr(), self.val()) ) &&
            abs_inv(self.abs_post, r.val().mem) &&
            ( abs_inv(self.abs_pre, r.val().crash) ||
              abs_inv(self.abs_post, r.val().crash) )
        }

        proof fn apply(tracked self, tracked r: FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: (FractionalResource<MemCrashView, 2>, FractionalResource<MemCrashView, 2>))
        {
            let tracked mut sf = self.frac;
            sf.combine_mut(r);
            sf.update_mut(MemCrashView{
                    mem: view_write(r.val().mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(r.val().crash, self.addr(), self.val()) } else { r.val().crash },
                });
            let tracked r = sf.split_mut(1);
            (r, sf)
        }
    }

    pub struct WriteFupd1
    {
        pub v: u8,
        pub tracked frac: FractionalResource<MemCrashView, 2>,
        pub ghost abs: AbsView,
    }

    impl DiskWritePermission<FractionalResource<MemCrashView, 2>> for WriteFupd1
    {
        open spec fn id(&self) -> int { self.frac.id() }
        open spec fn addr(&self) -> u8 { 1 }
        open spec fn val(&self) -> u8 { self.v }

        open spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.frac.frac() == 1 &&
            self.val() >= self.abs &&
            abs_inv(self.abs, self.frac.val().mem) &&
            abs_inv(self.abs, self.frac.val().crash)
        }

        open spec fn post(&self, r: FractionalResource<MemCrashView, 2>) -> bool {
            r.valid(self.id(), 1) &&
            r.val().mem == view_write(self.frac.val().mem, self.addr(), self.val()) &&
            ( r.val().crash == self.frac.val().crash ||
              r.val().crash == view_write(self.frac.val().crash, 1, self.val()) ) &&
            abs_inv(self.abs, r.val().mem) &&
            abs_inv(self.abs, r.val().crash)
        }

        proof fn apply(tracked self, tracked r: FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: (FractionalResource<MemCrashView, 2>, FractionalResource<MemCrashView, 2>))
        {
            let tracked mut sf = self.frac;
            sf.combine_mut(r);
            sf.update_mut(MemCrashView{
                    mem: view_write(r.val().mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(r.val().crash, self.addr(), self.val()) } else { r.val().crash },
                });
            let tracked r = sf.split_mut(1);
            (r, sf)
        }
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::alloc();

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 0);

        let tracked fupd = WriteFupd{ a: 1u8, v: 5u8, frac: r, abs_pre: 0, abs_post: 0 };
        let Tracked(r) = d.write::<_, WriteFupd>(1, 5, Tracked(fupd));

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 5);

        // As another example, could use a different fupd to justify the write.
        let tracked fupd = WriteFupd1{ v: 7u8, frac: r, abs: 0 };
        let Tracked(r) = d.write::<_, WriteFupd1>(1, 7, Tracked(fupd));

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 7);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        d.barrier_owned(Tracked(&r));

        let tracked fupd = WriteFupd{ a: 0u8, v: 2u8, frac: r, abs_pre: 0, abs_post: 2 };
        let Tracked(r) = d.write::<_, WriteFupd>(0, 2, Tracked(fupd));

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 2 && x1 == 7);

        ()
    }
}
