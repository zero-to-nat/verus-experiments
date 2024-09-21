use builtin::*;
use vstd::prelude::*;
use vstd::invariant::*;

pub mod frac;

use frac::FractionalResource;

verus! {
    pub const DISK_INV_NS: u64 = 12345;

    pub type DiskView = (u8, u8);

    pub open spec fn view_write(state: DiskView, addr: u8, val: u8) -> DiskView
    {
        if addr == 0 {
            (val, state.1)
        } else {
            (state.0, val)
        }
    }

    pub open spec fn view_read(state: DiskView, addr: u8) -> u8
    {
        if addr == 0 {
            state.0
        } else {
            state.1
        }
    }

    pub struct MemCrashView
    {
        pub mem: DiskView,
        pub crash: DiskView,
    }

    pub trait DiskWritePermission<ResultT> where Self: Sized {
        spec fn addr(&self) -> u8;
        spec fn val(&self) -> u8;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: ResultT) -> bool;
        proof fn apply(tracked self, tracked r: &mut FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: ResultT)
            requires
                self.pre(),
                old(r).valid(self.id(), 1),
            ensures
                r.valid(self.id(), 1),
                r.val() == (MemCrashView{
                    mem: view_write(old(r).val().mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(old(r).val().crash, self.addr(), self.val()) } else { old(r).val().crash },
                }),
                self.post(result),
            opens_invariants
                [ DISK_INV_NS ];
    }

    pub trait DiskBarrierPermission<ResultT> where Self: Sized {
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: ResultT) -> bool;
        proof fn apply(tracked self, tracked r: &mut FractionalResource<MemCrashView, 2>, tracked credit: OpenInvariantCredit) -> (tracked result: ResultT)
            requires
                self.pre(),
                old(r).valid(self.id(), 1),
                old(r).val().mem == old(r).val().crash,
            ensures
                r.valid(self.id(), 1),
                r.val() == old(r).val(),
                self.post(result),
            opens_invariants
                [ DISK_INV_NS ];
    }

    pub trait DiskReadPermission<ResultT> where Self: Sized {
        spec fn addr(&self) -> u8;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: ResultT, v: u8) -> bool;
        proof fn validate(tracked &self, tracked r: &mut FractionalResource<MemCrashView, 2>, tracked credit: OpenInvariantCredit)
            requires
                self.pre(),
                old(r).valid(self.id(), 1),
            ensures
                self.addr() == 0 || self.addr() == 1,
                r.valid(self.id(), 1),
                r.val() == old(r).val(),
            opens_invariants
                [ DISK_INV_NS ];
        proof fn apply(tracked self, tracked r: &mut FractionalResource<MemCrashView, 2>, v: u8, tracked credit: OpenInvariantCredit) -> (tracked result: ResultT)
            requires
                self.pre(),
                old(r).valid(self.id(), 1),
                v == view_read(old(r).val().mem, self.addr()),
            ensures
                r.valid(self.id(), 1),
                r.val() == old(r).val(),
                self.post(result, v),
            opens_invariants
                [ DISK_INV_NS ];
    }

    pub struct Disk
    {
        block0: u8,
        block1: u8,
        ghost durable: DiskView,    // Prophecy-style crash state
        frac: Tracked<FractionalResource<MemCrashView, 2>>,
    }

    impl Disk
    {
        pub closed spec fn inv(&self) -> bool
        {
            self.frac@.inv() &&
            self.frac@.val().crash == self.durable &&
            self.frac@.val().mem == (self.block0, self.block1) &&
            self.frac@.frac() == 1
        }

        pub closed spec fn id(&self) -> int
        {
            self.frac@.id()
        }

        pub fn alloc() -> (res: (Disk, Tracked<FractionalResource::<MemCrashView, 2>>))
            requires
                true,
            ensures
                res.0.inv(),
                res.1@.valid(res.0.id(), 1),
                res.1@.val() == (MemCrashView{
                    mem: (0, 0),
                    crash: (0, 0),
                }),
        {
            let tracked r = FractionalResource::<MemCrashView, 2>::alloc(MemCrashView{
                mem: (0, 0),
                crash: (0, 0),
            });
            let tracked (r1, r2) = r.split(1);
            let mut d = Disk{
                block0: 0,
                block1: 0,
                durable: (0, 0),
                frac: Tracked(r1),
            };
            (d, Tracked(r2))
        }

        // Leftover, should really be implemented in terms of the fupd-style read() below.
        pub fn read_owned(&self, addr: u8, Tracked(f): Tracked<&mut FractionalResource<MemCrashView, 2>>) -> (result: u8)
            requires
                self.inv(),
                old(f).inv(),
                old(f).id() == self.id(),
            ensures
                result == view_read(f.val().mem, addr),
                f == old(f),
        {
            proof {
                f.agree(self.frac.borrow())
            };
            if addr == 0 {
                self.block0
            } else {
                self.block1
            }
        }

        pub fn read<ResultT, Perm>(&mut self, addr: u8, Tracked(perm): Tracked<Perm>) -> (result: (u8, Tracked<ResultT>))
            where
                Perm: DiskReadPermission<ResultT>
            requires
                old(self).inv(),
                perm.pre(),
                perm.addr() == addr,
                perm.id() == old(self).id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.post(result.1@, result.0),
        {
            // Just to make sure validation works, try to invoke validate().
            let credit = create_open_invariant_credit();
            proof {
                perm.validate(self.frac.borrow_mut(), credit.get())
            };

            let v = if addr == 0 { self.block0 } else { self.block1 };
            let credit = create_open_invariant_credit();
            (v, Tracked(perm.apply(self.frac.borrow_mut(), v, credit.get())))
        }

        pub fn write<ResultT, Perm>(&mut self, addr: u8, val: u8, Tracked(perm): Tracked<Perm>) -> (result: Tracked<ResultT>)
            where
                Perm: DiskWritePermission<ResultT>
            requires
                old(self).inv(),
                perm.pre(),
                perm.addr() == addr,
                perm.val() == val,
                perm.id() == old(self).id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.post(result@),
        {
            if addr == 0 {
                self.block0 = val
            } else {
                self.block1 = val
            };
            let credit = create_open_invariant_credit();
            Tracked({
                let write_crash = vstd::pervasive::arbitrary();
                if write_crash {
                    self.durable = view_write(self.durable, addr, val)
                };
                perm.apply(self.frac.borrow_mut(), write_crash, credit.get())
            })
        }

        // Leftover, should really be implemented in terms of the fupd-style barrier() below
        #[verifier(external_body)]
        pub fn barrier_owned(&self, Tracked(f): Tracked<&FractionalResource::<MemCrashView, 2>>)
            requires
                self.inv(),
                f.valid(self.id(), 1),
            ensures
                f.val().crash == f.val().mem,
        {
            unimplemented!()
        }

        pub fn barrier<ResultT, Perm>(&mut self, Tracked(perm): Tracked<Perm>) -> (result: Tracked<ResultT>)
            where
                Perm: DiskBarrierPermission<ResultT>
            requires
                old(self).inv(),
                perm.pre(),
                perm.id() == old(self).id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.post(result@),
        {
            assert(self.durable == (self.block0, self.block1)) by { admit() };

            let credit = create_open_invariant_credit();
            Tracked(perm.apply(self.frac.borrow_mut(), credit.get()))
        }
    }

    fn main()
    {
        let (d, Tracked(r)) = Disk::alloc();
        let mut d = d;

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 0);

        ()
    }
}
