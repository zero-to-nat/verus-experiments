use builtin::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::proph::*;

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

    pub trait DiskWritePermission where Self: Sized {
        type Result;

        spec fn addr(&self) -> u8;
        spec fn val(&self) -> u8;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result) -> bool;
        proof fn apply(tracked self, tracked r: &mut FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
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

    pub trait DiskBarrierPermission where Self: Sized {
        type Result;

        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result) -> bool;
        proof fn apply(tracked self, tracked r: &FractionalResource<MemCrashView, 2>, tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                r.val().mem == r.val().crash,
            ensures
                self.post(result),
            opens_invariants
                [ DISK_INV_NS ];
    }

    pub trait DiskReadPermission where Self: Sized {
        type Result;

        spec fn addr(&self) -> u8;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result, v: u8) -> bool;
        proof fn validate(tracked &self, tracked r: &FractionalResource<MemCrashView, 2>, tracked credit: OpenInvariantCredit)
            requires
                self.pre(),
                r.valid(self.id(), 1),
            ensures
                self.addr() == 0 || self.addr() == 1,
            opens_invariants
                [ DISK_INV_NS ];
        proof fn apply(tracked self, tracked r: &FractionalResource<MemCrashView, 2>, v: u8, tracked credit: OpenInvariantCredit) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                v == view_read(r.val().mem, self.addr()),
            ensures
                self.post(result, v),
            opens_invariants
                [ DISK_INV_NS ];
    }

    pub struct Disk
    {
        block0: Vec<u8>,
        block1: Vec<u8>,
        ghost durable: DiskView,    // Prophecy-style crash state
        frac: Tracked<FractionalResource<MemCrashView, 2>>,

        // proph0/proph1 predict which value in prev0/prev1 will be durably
        // written to disk.  An out-of-bounds value predicts block0/block1.
        proph0: Prophecy::<usize>,
        proph1: Prophecy::<usize>,
    }

    pub open spec fn proph_valid(p: Prophecy::<usize>, b: Vec<u8>, d: u8) -> bool {
        if 0 <= p@ < b.len() {
            d == b[p@ as int]
        } else {
            d == b[0]
        }
    }

    #[verifier::external_body]
    pub exec fn choose_usize(max: usize) -> (result: usize)
        ensures
            0 <= result < max
    {
        unimplemented!()
    }

    impl Disk
    {
        pub closed spec fn inv(&self) -> bool
        {
            self.block0.len() > 0 &&
            self.block1.len() > 0 &&
            self.frac@.inv() &&
            self.frac@.val().crash == self.durable &&
            self.frac@.val().mem == (self.block0[self.block0.len()-1], self.block1[self.block1.len()-1]) &&
            self.frac@.frac() == 1 &&
            proph_valid(self.proph0, self.block0, self.durable.0) &&
            proph_valid(self.proph1, self.block1, self.durable.1)
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
                block0: vec![0],
                block1: vec![0],
                durable: (0, 0),
                frac: Tracked(r1),
                proph0: Prophecy::<usize>::alloc(),
                proph1: Prophecy::<usize>::alloc(),
            };
            (d, Tracked(r2))
        }

        // Leftover, should really be implemented in terms of the fupd-style read() below.
        pub fn read_owned(&self, addr: u8, Tracked(f): Tracked<&FractionalResource<MemCrashView, 2>>) -> (result: u8)
            requires
                self.inv(),
                f.inv(),
                f.id() == self.id(),
            ensures
                result == view_read(f.val().mem, addr),
        {
            proof {
                f.agree(self.frac.borrow())
            };
            if addr == 0 {
                self.block0[self.block0.len()-1]
            } else {
                self.block1[self.block1.len()-1]
            }
        }

        pub fn read<Perm>(&mut self, addr: u8, Tracked(perm): Tracked<Perm>) -> (result: (u8, Tracked<Perm::Result>))
            where
                Perm: DiskReadPermission
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

            let v = if addr == 0 { self.block0[self.block0.len()-1] } else { self.block1[self.block1.len()-1] };
            let credit = create_open_invariant_credit();
            (v, Tracked(perm.apply(self.frac.borrow_mut(), v, credit.get())))
        }

        pub fn write<Perm>(&mut self, addr: u8, val: u8, Tracked(perm): Tracked<Perm>) -> (result: Tracked<Perm::Result>)
            where
                Perm: DiskWritePermission
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
                self.block0.push(val);
            } else {
                self.block1.push(val);
            };
            let credit = create_open_invariant_credit();
            Tracked({
                let mut write_crash = true;

                if addr == 0 {
                    write_crash = (self.proph0@ == self.block0.len()-1);
                } else {
                    write_crash = (self.proph1@ == self.block1.len()-1);
                }

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

        pub fn barrier<Perm>(&mut self, Tracked(perm): Tracked<Perm>) -> (result: Tracked<Perm::Result>)
            where
                Perm: DiskBarrierPermission
            requires
                old(self).inv(),
                perm.pre(),
                perm.id() == old(self).id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.post(result@),
        {
            let mut proph0 = Prophecy::<usize>::alloc();
            let mut proph1 = Prophecy::<usize>::alloc();

            std::mem::swap(&mut self.proph0, &mut proph0);
            std::mem::swap(&mut self.proph1, &mut proph1);

            proph0.resolve(self.block0.len()-1);
            proph1.resolve(self.block1.len()-1);

            self.block0 = vec![self.block0[self.block0.len()-1]];
            self.block1 = vec![self.block1[self.block1.len()-1]];

            assert(self.durable == (self.block0[0], self.block1[0]));

            let credit = create_open_invariant_credit();
            Tracked(perm.apply(self.frac.borrow_mut(), credit.get()))
        }

        pub fn crash(&mut self)
            requires
                old(self).inv()
        {
            let crashidx0 = choose_usize(self.block0.len());
            let crashidx1 = choose_usize(self.block1.len());

            let mut proph0 = Prophecy::<usize>::alloc();
            let mut proph1 = Prophecy::<usize>::alloc();

            std::mem::swap(&mut self.proph0, &mut proph0);
            std::mem::swap(&mut self.proph1, &mut proph1);

            proph0.resolve(crashidx0);
            proph1.resolve(crashidx1);

            let Ghost(crash0) = Ghost(self.block0[crashidx0 as int]);
            let Ghost(crash1) = Ghost(self.block1[crashidx1 as int]);
            let Ghost(crash) = Ghost((crash0, crash1));

            assert(crash == self.durable);
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
