use builtin::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::proph::*;

pub mod frac;

use frac::Frac;

verus! {
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

        spec fn namespace(&self) -> int;
        spec fn addr(&self) -> u8;
        spec fn val(&self) -> u8;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result) -> bool;
        proof fn apply(tracked self, tracked r: &mut Frac<MemCrashView>, write_crash: bool) -> (tracked result: Self::Result)
            requires
                self.pre(),
                old(r).valid(self.id(), 1),
            ensures
                r.valid(self.id(), 1),
                r@ == (MemCrashView{
                    mem: view_write(old(r)@.mem, self.addr(), self.val()),
                    crash: if write_crash { view_write(old(r)@.crash, self.addr(), self.val()) } else { old(r)@.crash },
                }),
                self.post(result),
            opens_invariants
                [ self.namespace() ];
    }

    pub trait DiskBarrierPermission where Self: Sized {
        type Result;

        spec fn namespace(&self) -> int;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result) -> bool;
        proof fn apply(tracked self, tracked r: &Frac<MemCrashView>) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                r@.mem == r@.crash,
            ensures
                self.post(result),
            opens_invariants
                [ self.namespace() ];
    }

    pub trait DiskReadPermission where Self: Sized {
        type Result;

        spec fn namespace(&self) -> int;
        spec fn addr(&self) -> u8;
        spec fn id(&self) -> int;
        spec fn pre(&self) -> bool;
        spec fn post(&self, r: Self::Result, v: u8) -> bool;
        proof fn validate(tracked &self, tracked r: &Frac<MemCrashView>, tracked credit: OpenInvariantCredit)
            requires
                self.pre(),
                r.valid(self.id(), 1),
            ensures
                self.addr() == 0 || self.addr() == 1,
            opens_invariants
                [ self.namespace() ];
        proof fn apply(tracked self, tracked r: &Frac<MemCrashView>, v: u8) -> (tracked result: Self::Result)
            requires
                self.pre(),
                r.valid(self.id(), 1),
                v == view_read(r@.mem, self.addr()),
            ensures
                self.post(result, v),
            opens_invariants
                [ self.namespace() ];
    }

    pub struct Disk
    {
        block0: Vec<u8>,
        block1: Vec<u8>,
        ghost durable: DiskView,    // Prophecy-style crash state
        frac: Tracked<Frac<MemCrashView>>,

        // proph0/proph1 predict which value in prev0/prev1 will be durably
        // written to disk.  If the value is not equal to any of the pending
        // writes, that means a prediction for the first value.
        proph0: Prophecy::<u8>,
        proph1: Prophecy::<u8>,
    }

    pub open spec fn proph_value(b: Vec<u8>, p: Prophecy::<u8>) -> u8 {
        if b@.contains(p@) {
            p@
        } else {
            b[0]
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
            self.frac@@.crash == self.durable &&
            self.frac@@.mem == (self.block0[self.block0.len()-1], self.block1[self.block1.len()-1]) &&
            self.frac@.frac() == 1 &&
            self.durable.0 == proph_value(self.block0, self.proph0) &&
            self.durable.1 == proph_value(self.block1, self.proph1)
        }

        pub closed spec fn id(&self) -> int
        {
            self.frac@.id()
        }

        pub fn new() -> (res: (Disk, Tracked<Frac::<MemCrashView>>))
            requires
                true,
            ensures
                res.0.inv(),
                res.1@.valid(res.0.id(), 1),
                res.1@@ == (MemCrashView{
                    mem: (0, 0),
                    crash: (0, 0),
                }),
        {
            let tracked r = Frac::<MemCrashView>::new(MemCrashView{
                mem: (0, 0),
                crash: (0, 0),
            });
            let tracked (r1, r2) = r.split(1);
            let mut d = Disk{
                block0: vec![0],
                block1: vec![0],
                durable: (0, 0),
                frac: Tracked(r1),
                proph0: Prophecy::<u8>::new(),
                proph1: Prophecy::<u8>::new(),
            };
            (d, Tracked(r2))
        }

        // Leftover, should really be implemented in terms of the fupd-style read() below.
        pub fn read_owned(&self, addr: u8, Tracked(f): Tracked<&Frac<MemCrashView>>) -> (result: u8)
            requires
                self.inv(),
                f.inv(),
                f.id() == self.id(),
            returns
                view_read(f@.mem, addr)
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
            (v, Tracked(perm.apply(self.frac.borrow_mut(), v)))
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
                assert(self.block0@[self.block0.len() - 1] == val);
            } else {
                self.block1.push(val);
                assert(self.block1@[self.block1.len() - 1] == val);
            };
            Tracked({
                let mut write_crash = true;

                if addr == 0 {
                    write_crash = (self.proph0@ == val);
                } else {
                    write_crash = (self.proph1@ == val);
                }

                if write_crash {
                    self.durable = view_write(self.durable, addr, val)
                };

                if addr == 0 {
                    vstd::seq_lib::lemma_seq_contains_after_push(old(self).block0@, val, self.proph0@);
                    assert(self.durable.0 == proph_value(self.block0, self.proph0));
                    assert(self.durable.1 == proph_value(self.block1, self.proph1));
                } else {
                    vstd::seq_lib::lemma_seq_contains_after_push(old(self).block1@, val, self.proph1@);
                    assert(self.durable.0 == proph_value(self.block0, self.proph0));
                    assert(self.durable.1 == proph_value(self.block1, self.proph1));
                }

                perm.apply(self.frac.borrow_mut(), write_crash)
            })
        }

        // Leftover, should really be implemented in terms of the fupd-style barrier() below
        #[verifier(external_body)]
        pub fn barrier_owned(&self, Tracked(f): Tracked<&Frac::<MemCrashView>>)
            requires
                self.inv(),
                f.valid(self.id(), 1),
            ensures
                f@.crash == f@.mem,
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
            let mut proph0 = Prophecy::<u8>::new();
            let mut proph1 = Prophecy::<u8>::new();

            std::mem::swap(&mut self.proph0, &mut proph0);
            std::mem::swap(&mut self.proph1, &mut proph1);

            proph0.resolve(&self.block0[self.block0.len()-1]);
            proph1.resolve(&self.block1[self.block1.len()-1]);

            self.block0 = vec![self.block0[self.block0.len()-1]];
            self.block1 = vec![self.block1[self.block1.len()-1]];

            assert(self.durable == (self.block0[0], self.block1[0]));
            Tracked(perm.apply(self.frac.borrow_mut()))
        }

        pub fn crash(self)
            requires
                self.inv()
        {
            let mut mself = self;

            let crashidx0 = choose_usize(mself.block0.len());
            let crashidx1 = choose_usize(mself.block1.len());

            let crash0 = mself.block0[crashidx0];
            let crash1 = mself.block1[crashidx1];

            mself.proph0.resolve(&crash0);
            mself.proph1.resolve(&crash1);

            let Ghost(crash) = Ghost((crash0, crash1));
            assert(crash == mself.durable);
        }
    }

    fn main()
    {
        let (d, Tracked(r)) = Disk::new();
        let mut d = d;

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 0);

        ()
    }
}
