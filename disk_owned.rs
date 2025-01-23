use builtin::*;
use vstd::prelude::*;

mod disk;

use disk::DiskView;
use disk::MemCrashView;
use disk::view_write;
use disk::frac;
use frac::Frac;
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
        pub tracked frac: Frac<MemCrashView>,
        pub ghost abs_pre: AbsView,
        pub ghost abs_post: AbsView,
    }

    impl DiskWritePermission for WriteFupd
    {
        type Result = Frac<MemCrashView>;

        open spec fn namespace(&self) -> int { 0 }
        open spec fn id(&self) -> int { self.frac.id() }
        open spec fn addr(&self) -> u8 { self.a }
        open spec fn val(&self) -> u8 { self.v }

        open spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.frac.frac() == 1 &&
            if self.addr() == 0 {
                self.abs_post == self.val() &&
                self.val() <= self.frac@.mem.1 &&
                self.val() <= self.frac@.crash.1
            } else {
                self.abs_post == self.abs_pre &&
                self.val() >= self.abs_pre
            } &&
            abs_inv(self.abs_pre, self.frac@.mem) &&
            abs_inv(self.abs_pre, self.frac@.crash)
        }

        open spec fn post(&self, r: Frac<MemCrashView>) -> bool {
            r.valid(self.id(), 1) &&
            r@.mem == view_write(self.frac@.mem, self.addr(), self.val()) &&
            ( r@.crash == self.frac@.crash ||
              r@.crash == view_write(self.frac@.crash, self.addr(), self.val()) ) &&
            abs_inv(self.abs_post, r@.mem) &&
            ( abs_inv(self.abs_pre, r@.crash) ||
              abs_inv(self.abs_post, r@.crash) )
        }

        proof fn apply(tracked self, tracked r: &mut Frac<MemCrashView>, write_crash: bool) -> (tracked result: Frac<MemCrashView>)
        {
            r.combine(self.frac);
            r.update(MemCrashView{
                    mem: view_write(r@.mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(r@.crash, self.addr(), self.val()) } else { r@.crash },
                });
            r.split(1)
        }
    }

    pub struct WriteFupd1
    {
        pub v: u8,
        pub tracked frac: Frac<MemCrashView>,
        pub ghost abs: AbsView,
    }

    impl DiskWritePermission for WriteFupd1
    {
        type Result = Frac<MemCrashView>;

        open spec fn namespace(&self) -> int { 0 }
        open spec fn id(&self) -> int { self.frac.id() }
        open spec fn addr(&self) -> u8 { 1 }
        open spec fn val(&self) -> u8 { self.v }

        open spec fn pre(&self) -> bool {
            self.frac.inv() &&
            self.frac.frac() == 1 &&
            self.val() >= self.abs &&
            abs_inv(self.abs, self.frac@.mem) &&
            abs_inv(self.abs, self.frac@.crash)
        }

        open spec fn post(&self, r: Frac<MemCrashView>) -> bool {
            r.valid(self.id(), 1) &&
            r@.mem == view_write(self.frac@.mem, self.addr(), self.val()) &&
            ( r@.crash == self.frac@.crash ||
              r@.crash == view_write(self.frac@.crash, 1, self.val()) ) &&
            abs_inv(self.abs, r@.mem) &&
            abs_inv(self.abs, r@.crash)
        }

        proof fn apply(tracked self, tracked r: &mut Frac<MemCrashView>, write_crash: bool) -> (tracked result: Frac<MemCrashView>)
        {
            r.combine(self.frac);
            r.update(MemCrashView{
                    mem: view_write(r@.mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(r@.crash, self.addr(), self.val()) } else { r@.crash },
                });
            r.split(1)
        }
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::new();

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 0);

        let tracked fupd = WriteFupd{ a: 1u8, v: 5u8, frac: r, abs_pre: 0, abs_post: 0 };
        let Tracked(r) = d.write::<WriteFupd>(1, 5, Tracked(fupd));

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 5);

        // As another example, could use a different fupd to justify the write.
        let tracked fupd = WriteFupd1{ v: 7u8, frac: r, abs: 0 };
        let Tracked(r) = d.write::<WriteFupd1>(1, 7, Tracked(fupd));

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 7);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        d.barrier_owned(Tracked(&r));

        let tracked fupd = WriteFupd{ a: 0u8, v: 2u8, frac: r, abs_pre: 0, abs_post: 2 };
        let Tracked(r) = d.write::<WriteFupd>(0, 2, Tracked(fupd));

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 2 && x1 == 7);

        ()
    }
}
