use builtin::*;
use vstd::prelude::*;
use vstd::modes::*;
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
        a: u8,
        v: u8,
        tracked frac: Option<FractionalResource<MemCrashView, 2>>,
        ghost invoked: bool,
        ghost abs_pre: AbsView,
        ghost abs_post: AbsView,
        ghost pre: MemCrashView,
    }

    impl DiskWritePermission<MemCrashView> for WriteFupd
    {
        closed spec fn inv(&self) -> bool {
            self.frac.is_Some() &&
            self.frac.unwrap().inv() &&
            self.frac.unwrap().frac() == 1 &&
            self.frac.unwrap().val().mem == if !self.invoked() { self.pre.mem } else { view_write(self.pre.mem, self.addr(), self.val()) } &&
            ( self.frac.unwrap().val().crash == self.pre.crash ||
              ( self.invoked() && self.frac.unwrap().val().crash == view_write(self.pre.crash, self.addr(), self.val()) ) ) &&
            if self.addr() == 0 {
                self.val() == self.abs_post &&
                self.val() <= self.frac.unwrap().val().mem.1 &&
                self.val() <= self.frac.unwrap().val().crash.1
            } else {
                self.abs_post == self.abs_pre && self.val() >= self.abs_pre
            } &&
            abs_inv(if self.invoked() { self.abs_post } else { self.abs_pre }, self.frac.unwrap().val().mem) &&
            ( abs_inv(self.abs_pre, self.frac.unwrap().val().crash) ||
              abs_inv(self.abs_post, self.frac.unwrap().val().crash) )
        }

        closed spec fn id(&self) -> int {
            self.frac.unwrap().id()
        }

        closed spec fn addr(&self) -> u8 {
            self.a
        }

        closed spec fn val(&self) -> u8 {
            self.v
        }

        closed spec fn invoked(&self) -> bool {
            self.invoked
        }

        closed spec fn pre(&self) -> MemCrashView {
            self.pre
        }

        proof fn apply(tracked &mut self, tracked r: FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: FractionalResource<MemCrashView, 2>)
        {
            let tracked mut opt_frac = None;
            tracked_swap(&mut self.frac, &mut opt_frac);
            let tracked r = r.combine(opt_frac.tracked_unwrap());
            let tracked r = r.update(MemCrashView{
                    mem: view_write(r.val().mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(r.val().crash, self.addr(), self.val()) } else { r.val().crash },
                });
            let tracked (r1, r2) = r.split(1);
            self.frac = Some(r2);
            self.invoked = true;
            r1
        }
    }

    impl WriteFupd
    {
        proof fn alloc(tracked addr: u8, tracked val: u8, tracked frac: FractionalResource<MemCrashView, 2>, tracked pre: AbsView, tracked post: AbsView) -> (tracked res: WriteFupd)
            requires
                frac.inv(),
                frac.frac() == 1,
                abs_inv(pre, frac.val().mem),
                abs_inv(pre, frac.val().crash),
                if addr == 0 {
                    val == post && val <= frac.val().mem.1 && val <= frac.val().crash.1
                } else {
                    pre == post && val >= pre
                },
            ensures
                res.inv(),
                !res.invoked(),
                res.id() == frac.id(),
                res.addr() == addr,
                res.val() == val,
                res.pre() == frac.val(),
        {
            let tracked mut f = WriteFupd{
                a: addr,
                v: val,
                frac: Some(frac),
                invoked: false,
                abs_pre: pre,
                abs_post: post,
                pre: frac.val(),
            };
            f
        }

        proof fn frac(tracked self) -> (tracked res: Option<FractionalResource<MemCrashView, 2>>)
            requires
                self.invoked(),
                self.inv(),
            ensures
                res.is_Some(),
                res.unwrap().inv(),
                res.unwrap().frac() == 1,
                res.unwrap().id() == self.id(),
                res.unwrap().val().mem == view_write(self.pre().mem, self.addr(), self.val()),
                ( res.unwrap().val().crash == self.pre().crash ||
                  res.unwrap().val().crash == view_write(self.pre().crash, self.addr(), self.val()) ),
        {
            self.frac
        }
    }

    pub struct WriteFupd1
    {
        v: u8,
        tracked frac: Option<FractionalResource<MemCrashView, 2>>,
        ghost invoked: bool,
        ghost abs: AbsView,
        ghost pre: MemCrashView,
    }

    impl DiskWritePermission<MemCrashView> for WriteFupd1
    {
        closed spec fn inv(&self) -> bool {
            self.frac.is_Some() &&
            self.frac.unwrap().inv() &&
            self.frac.unwrap().frac() == 1 &&
            self.frac.unwrap().val().mem == if !self.invoked() { self.pre.mem } else { view_write(self.pre.mem, self.addr(), self.val()) } &&
            ( self.frac.unwrap().val().crash == self.pre.crash ||
              ( self.invoked() && self.frac.unwrap().val().crash == view_write(self.pre.crash, 1, self.val()) ) ) &&
            self.val() >= self.abs &&
            abs_inv(self.abs, self.frac.unwrap().val().mem) &&
            abs_inv(self.abs, self.frac.unwrap().val().crash)
        }

        closed spec fn id(&self) -> int { self.frac.unwrap().id() }
        closed spec fn addr(&self) -> u8 { 1 }
        closed spec fn val(&self) -> u8 { self.v }
        closed spec fn invoked(&self) -> bool { self.invoked }
        closed spec fn pre(&self) -> MemCrashView { self.pre }

        proof fn apply(tracked &mut self, tracked r: FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: FractionalResource<MemCrashView, 2>)
        {
            let tracked mut opt_frac = None;
            tracked_swap(&mut self.frac, &mut opt_frac);
            let tracked r = r.combine(opt_frac.tracked_unwrap());
            let tracked r = r.update(MemCrashView{
                    mem: view_write(r.val().mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(r.val().crash, self.addr(), self.val()) } else { r.val().crash },
                });
            let tracked (r1, r2) = r.split(1);
            self.frac = Some(r2);
            self.invoked = true;
            r1
        }
    }

    impl WriteFupd1
    {
        proof fn alloc(tracked val: u8, tracked frac: FractionalResource<MemCrashView, 2>, tracked abs: AbsView) -> (tracked res: WriteFupd1)
            requires
                frac.inv(),
                frac.frac() == 1,
                abs_inv(abs, frac.val().mem),
                abs_inv(abs, frac.val().crash),
                val >= abs,
            ensures
                res.inv(),
                !res.invoked(),
                res.id() == frac.id(),
                res.addr() == 1,
                res.val() == val,
                res.pre() == frac.val(),
        {
            let tracked mut f = WriteFupd1{
                v: val,
                frac: Some(frac),
                invoked: false,
                abs: abs,
                pre: frac.val(),
            };
            f
        }

        proof fn frac(tracked self) -> (tracked res: Option<FractionalResource<MemCrashView, 2>>)
            requires
                self.invoked(),
                self.inv(),
            ensures
                res.is_Some(),
                res.unwrap().inv(),
                res.unwrap().frac() == 1,
                res.unwrap().id() == self.id(),
                res.unwrap().val().mem == view_write(self.pre().mem, self.addr(), self.val()),
                ( res.unwrap().val().crash == self.pre().crash ||
                  res.unwrap().val().crash == view_write(self.pre().crash, self.addr(), self.val()) ),
        {
            self.frac
        }
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::alloc();

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 0);

        let tracked fupd = WriteFupd::alloc(1u8, 5u8, r, 0u8, 0u8);
        d.write::<_, WriteFupd>(1, 5, Tracked(&mut fupd));
        let tracked r = fupd.frac().tracked_unwrap();

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 5);

        // As another example, could use a different fupd to justify the write.
        let tracked fupd = WriteFupd1::alloc(7u8, r, 0u8);
        d.write::<_, WriteFupd1>(1, 7, Tracked(&mut fupd));
        let tracked r = fupd.frac().tracked_unwrap();

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 7);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        d.barrier_owned(Tracked(&r));

        let tracked fupd = WriteFupd::alloc(0u8, 2u8, r, 0u8, 2u8);
        d.write::<_, WriteFupd>(0, 2, Tracked(&mut fupd));
        let tracked r = fupd.frac().tracked_unwrap();

        let x0 = d.read(0, Tracked(&mut r));
        let x1 = d.read(1, Tracked(&mut r));
        assert(x0 == 2 && x1 == 7);

        ()
    }
}
