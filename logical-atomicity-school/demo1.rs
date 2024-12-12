use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
// use vstd::modes::*;
use vstd::invariant::*;
use std::sync::Arc;
use vstd::thread::*;

mod frac;
use crate::frac::*;

verus!{

trait AtomicIncrementerIncrementCallback: Sized {
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, result: &Self::CBResult) -> bool
        ;

    proof fn increment_cb(tracked self, tracked rsrc: &mut FractionalResource<usize, 2>) -> (tracked out: Self::CBResult)
    requires
        old(rsrc).frac() == 1,
        old(rsrc).inv(),
        self.inv(),
        self.id() == old(rsrc).id()
    ensures
        rsrc.frac() == 1,
        rsrc.inv(),
        rsrc.val() == old(rsrc).val() + 1,
        rsrc.id() == old(rsrc).id(),
        self.post(&out),
    opens_invariants [ self.inv_namespace() ]
    ;
}

trait AtomicIncrementerGetCallback: Sized {
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn post(&self, return_val: usize, result: Self::CBResult) -> bool
        ;

    proof fn get_cb(tracked self, tracked rsrc: &FractionalResource<usize, 2>, return_val: usize) -> (tracked out: Self::CBResult)
    requires
        rsrc.frac() == 1,
        rsrc.inv(),
        self.inv(),
        self.id() == rsrc.id(),
        return_val == rsrc.val(),
    ensures
        self.post(return_val, out),
    ;
}

struct AtomicIncrementerInvK {
    up_id: int,
    down_id: int,
}

struct AtomicIncrementerInvV {
    up_frac: FractionalResource<usize, 2>,
    down_frac: FractionalResource<Seq<usize>, 2>,
}

struct AtomicIncrementerInvPred {
}

impl InvariantPredicate<AtomicIncrementerInvK, AtomicIncrementerInvV > for AtomicIncrementerInvPred {
    closed spec fn inv(k: AtomicIncrementerInvK, v: AtomicIncrementerInvV) -> bool
    {
        &&& v.up_frac.inv()
        &&& v.up_frac.id() == k.up_id
        &&& v.up_frac.frac() == 1

        &&& v.up_frac.val() == v.down_frac.val().len()

        &&& v.down_frac.inv()
        &&& v.down_frac.id() == k.down_id
        &&& v.down_frac.frac() == 1
    }
}

struct AtomicIncrementer {
    invariant: Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    log: SillyLog,
}

struct AtomicIncrementerIncrementCB<'a, UpCB: AtomicIncrementerIncrementCallback> {
    invariant: &'a Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    up_cb: UpCB,
    tracked credit: OpenInvariantCredit,
}

impl<'a, UpCB: AtomicIncrementerIncrementCallback> SillyLogInvAppendCallback for AtomicIncrementerIncrementCB<'a, UpCB> {
    type CBResult = UpCB::CBResult;

    spec fn pushed_value(&self) -> usize { 1 }

    spec fn id(&self) -> int {
        self.invariant@.constant().down_id
    }

    spec fn inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn other_namespace(&self) -> int { self.up_cb.inv_namespace() }

    spec fn inv(&self) -> bool
    {
        &&& self.up_cb.inv()
        &&& self.invariant@.constant().up_id == self.up_cb.id()
        &&& self.up_cb.inv_namespace() != self.inv_namespace()
    }

    proof fn append_cb(
        tracked self,
        tracked rsrc: &mut FractionalResource<Seq<usize>, 2>)
    -> tracked Self::CBResult
    {
        let tracked mut cb_result;
        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inner_val => {
            rsrc.combine_mut(inner_val.down_frac);
            let new_v = rsrc.val().push(1);
            rsrc.update_mut(new_v);
            assert( self.invariant@.namespace() != self.up_cb.inv_namespace() );
            cb_result = self.up_cb.increment_cb(&mut inner_val.up_frac);
            inner_val.down_frac = rsrc.split_mut(1);
        });

        cb_result
    }

    spec fn post(&self, result: &Self::CBResult) -> bool
    {
        &&& self.up_cb.post(result)
    }
}

struct AtomicIncrementerGetCB<'a, UpCB: AtomicIncrementerGetCallback> {
    invariant: &'a Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    up_cb: UpCB,
    tracked credit: OpenInvariantCredit,
}

impl<'a, UpCB: AtomicIncrementerGetCallback> SillyLogInvReadCallback for AtomicIncrementerGetCB<'a, UpCB> {
    type CBResult = UpCB::CBResult;

    spec fn id(&self) -> int {
        self.invariant@.constant().down_id
    }

    spec fn inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn inv(&self) -> bool
    {
        &&& self.up_cb.inv()
        &&& self.invariant@.constant().up_id == self.up_cb.id()
    }

    proof fn read_cb(
        tracked self,
        tracked rsrc: &FractionalResource<Seq<usize>, 2>,
        return_val: &Vec<usize>)
    -> tracked Self::CBResult
    {
        let tracked mut cb_result;
        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inner_val => {
            inner_val.down_frac.agree(rsrc);
            cb_result = self.up_cb.get_cb(/* missing credit*/ &mut inner_val.up_frac, return_val.len());
        });

        cb_result
    }

    spec fn post(&self, return_val: &Vec<usize>, result: &Self::CBResult) -> bool
    {
        &&& self.up_cb.post(return_val.len(), *result)
    }
}

impl AtomicIncrementer {
    spec fn id(&self) -> int {
        self.invariant@.constant().up_id
    }

    spec fn inv_namespace(self) -> int {
        12345
    }

    fn new() -> (out: (Self, Tracked<FractionalResource<usize, 2>>))
    ensures
        out.0.inv(),
        out.1@.inv(),
        out.1@.id() == out.0.id(),
        out.1@.frac() == 1,
        out.1@.val() == 0,
    {
        let (log, down_frac) = SillyLog::new();
        let tracked(up_frac, api_frac) = FractionalResource::alloc(0).split(1);

        let ghost inv_k = AtomicIncrementerInvK{up_id: up_frac.id(), down_id: log.id()};
        let tracked inv_v = AtomicIncrementerInvV{up_frac, down_frac: down_frac.get()};
        let tracked inv = AtomicInvariant::<_,_,AtomicIncrementerInvPred>::new(inv_k, inv_v, 12345);
        let result = AtomicIncrementer{invariant: Tracked(inv), log: log};
        (result, Tracked(api_frac))
    }

    spec fn inv(&self) -> bool
    {
        &&& self.invariant@.constant().down_id == self.log.id()
        // &&& self.caller_frac@.val().len() <= usize::MAX
        &&& self.invariant@.namespace() == self.inv_namespace()
    }

    fn increment<CB: AtomicIncrementerIncrementCallback>(&self, up_cb: Tracked<CB>)
        -> (out: Tracked<CB::CBResult>)
    requires
        self.inv(),
        up_cb@.inv(),
        up_cb@.id() == self.id(),
        up_cb@.inv_namespace() != self.inv_namespace(),
    ensures
        up_cb@.post(&out@),
    {
        let open_invariant_credit = create_open_invariant_credit();
        let down_cb:Tracked<AtomicIncrementerIncrementCB<CB>> = Tracked(AtomicIncrementerIncrementCB{invariant: &self.invariant, up_cb: up_cb.get(), credit: open_invariant_credit.get() });

        assert( down_cb@.inv() );
        self.log.append(1, down_cb)
    }
    
    fn get<CB: AtomicIncrementerGetCallback>(&self, up_cb: Tracked<CB>)
    -> (out: (usize, Tracked<CB::CBResult>))
    requires
        self.inv(),
        up_cb@.inv(),
        up_cb@.id() == self.id(),
    ensures
        up_cb@.post(out.0, out.1@),
    {
        let open_invariant_credit = create_open_invariant_credit();
        let down_cb:Tracked<AtomicIncrementerGetCB<CB>> = Tracked(AtomicIncrementerGetCB{invariant: &self.invariant, up_cb: up_cb.get(), credit: open_invariant_credit.get()});

        let (down_return_val, down_cb_result) = self.log.read(down_cb);
        (down_return_val.len(), down_cb_result)
    }
}

//////////////////////////////////////////////////////////////////////////////

struct SillyLogState {
    phy: Vec<usize>,
    abs: Tracked<FractionalResource<Seq<usize>, 2>>,
}

struct SillyLogPred {
    id: int,
}

impl RwLockPredicate<SillyLogState> for SillyLogPred {
    closed spec fn inv(self, v: SillyLogState) -> bool {
        &&& v.abs@.inv()    // internal inv for FractionalResource
        &&& v.abs@.frac() == 1
        &&& v.abs@.val() == v.phy@
        &&& v.abs@.id() == self.id
    }
}

struct SillyLog {
    locked_state: RwLock<SillyLogState, SillyLogPred>,
}

trait SillyLogInvAppendCallback: Sized {
    type CBResult;

    spec fn pushed_value(&self) -> usize
        ;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, result: &Self::CBResult) -> bool
        ;

    proof fn append_cb(
        tracked self,
        tracked rsrc: &mut FractionalResource<Seq<usize>, 2>)
    -> (tracked out: Self::CBResult)
    requires
        old(rsrc).frac() == 1,
        old(rsrc).inv(),
        self.inv(),
        self.id() == old(rsrc).id()
    ensures
        rsrc.frac() == 1,
        rsrc.inv(),
        rsrc.val() == old(rsrc).val().push(self.pushed_value()),
        self.post(&out),
        rsrc.id() == old(rsrc).id(),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

trait SillyLogInvReadCallback: Sized {
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, return_val: &Vec<usize>, result: &Self::CBResult) -> bool
        ;

    proof fn read_cb(
        tracked self,
        tracked rsrc: &FractionalResource<Seq<usize>, 2>,
        return_val: &Vec<usize>)
    -> (tracked out: Self::CBResult)
    requires
        rsrc.frac() == 1,
        rsrc.inv(),
        self.inv(),
        self.id() == rsrc.id(),
        return_val@ == rsrc.val(),
    ensures
        self.post(return_val, &out),
    opens_invariants [ self.inv_namespace() ]
    ;
}

impl SillyLog {
    spec fn id(&self) -> int { self.locked_state.pred().id }

    fn new() -> (out: (Self, Tracked<FractionalResource<Seq<usize>, 2>>))
    ensures
        out.1@.val() == Seq::<usize>::empty(),
        out.1@.inv(),
        out.1@.frac() == 1,
        out.1@.id() == out.0.id(),
    {
        let tracked(my_part, caller_part) = FractionalResource::alloc(Seq::empty()).split(1);

        let state = SillyLogState {
            phy: Vec::new(),
            abs: Tracked(my_part),
        };
        let ghost pred = SillyLogPred{id: state.abs@.id()};
        let locked_state = RwLock::new(state, Ghost(pred));
        let log = Self{ locked_state };
        (log, Tracked(caller_part))
    }

    fn append<CB: SillyLogInvAppendCallback>(&self, v: usize, cb: Tracked<CB>)
        -> (out: Tracked<CB::CBResult>)
    requires
        cb@.pushed_value() == v,
        cb@.inv(),
        cb@.id() == self.id(),
    ensures
        cb@.post(&out@),
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost old_state = state.abs@.val();
        state.phy.push(v);
        let cb_result = Tracked( cb.get().append_cb(state.abs.borrow_mut()) );
        lock_handle.release_write(state);
        cb_result
    }

    fn read<CB: SillyLogInvReadCallback>(&self, cb: Tracked<CB>)
    -> (out: (Vec<usize>, Tracked<CB::CBResult>))
    requires
        cb@.inv(),
        cb@.id() == self.id(),
    ensures
        cb@.post(&out.0, &out.1@),
    {
        let read_handle = self.locked_state.acquire_read();
        let phy_result = read_handle.borrow().phy.clone();
        let callee_frac = &read_handle.borrow().abs;

        let cbresult = Tracked({ cb.get().read_cb(&callee_frac.borrow(), &phy_result) });
        read_handle.release_read();

        (phy_result, cbresult)
    }
}

//////////////////////////////////////////////////////////////////////////////

struct MainInvK {
    down_id: int,
    thread_rsrc_ids: Map<usize, int>,
}

struct MainInvV {
    down_frac: FractionalResource<usize, 2>,
    thread_rsrcs: Map<usize, FractionalResource<usize, 2>>,
}

struct MainInvPred {}

impl InvariantPredicate<MainInvK, MainInvV> for MainInvPred {
    closed spec fn inv(k: MainInvK, v: MainInvV) -> bool
    {
        &&& v.down_frac.inv()
        &&& v.down_frac.id() == k.down_id
        &&& v.down_frac.frac() == 1

        &&& forall |idx| #[trigger] k.thread_rsrc_ids.contains_key(idx) ==> {
            &&& v.thread_rsrcs[idx].inv()
            &&& v.thread_rsrcs[idx].id() == k.thread_rsrc_ids[idx]
            &&& v.thread_rsrcs[idx].frac() == 1
            &&& v.thread_rsrcs[idx].val() <= 2
        }

        // there are exactly two threads
//         &&& forall |idx| thread_rsrcs.contains_key(idx) <==> { idx == 0 || idx == 1 }
        &&& k.thread_rsrc_ids.dom() == set![ 0usize, 1usize ]
        &&& v.thread_rsrcs.dom() == k.thread_rsrc_ids.dom()

        &&& v.down_frac.val() == v.thread_rsrcs[0].val() + v.thread_rsrcs[1].val()
    }
}

struct Main {
    invariant: Tracked<AtomicInvariant<MainInvK, MainInvV, MainInvPred>>,
    incrementer: AtomicIncrementer,
}

impl Main {
    spec fn inv(self) -> bool
    {
        &&& self.incrementer.inv()
        &&& self.invariant@.constant().thread_rsrc_ids.dom() == set![ 0usize, 1usize ]
        &&& self.invariant@.constant().down_id == self.incrementer.id()
        &&& self.inv_namespace() != self.incrementer.inv_namespace()
    }

    spec fn inv_namespace(&self) -> int { self.invariant@.namespace() }

    fn new() -> (out: (Self, Tracked<FractionalResource<usize, 2>>, Tracked<FractionalResource<usize, 2>>))
    ensures
        out.0.inv(),
        out.1@.valid(out.0.invariant@.constant().thread_rsrc_ids[0], 1),
        out.1@.val() == 0,
        out.2@.valid(out.0.invariant@.constant().thread_rsrc_ids[1], 1),
        out.2@.val() == 0,
    {
        let (incrementer, down_frac) = AtomicIncrementer::new();

        let tracked(left_inv_rsrc, left_thread_rsrc) = FractionalResource::alloc(0).split(1);
        let tracked(right_inv_rsrc, right_thread_rsrc) = FractionalResource::alloc(0).split(1);

        let ghost inv_k = MainInvK{
            down_id: incrementer.id(),
            thread_rsrc_ids: map![0 => left_inv_rsrc.id(), 1 => right_inv_rsrc.id()],
        };

        let mut thread_rsrcs = Tracked( Map::tracked_empty() );
        proof {
            thread_rsrcs.borrow_mut().tracked_insert(0, left_inv_rsrc);
            thread_rsrcs.borrow_mut().tracked_insert(1, right_inv_rsrc);
        }
        let tracked inv_v = MainInvV{
            down_frac: down_frac.get(),
            thread_rsrcs: thread_rsrcs.get()
        };

        assert( inv_v.down_frac.val() == 0 );
        assert( MainInvPred::inv(inv_k, inv_v) );
        let tracked inv = AtomicInvariant::<_,_,MainInvPred>::new(inv_k, inv_v, 12346);
 
        (Self{invariant: Tracked(inv), incrementer}, Tracked(left_thread_rsrc), Tracked(right_thread_rsrc))
    }

    fn spawn(aself: &Arc<Self>, thread_idx: usize, thread_rsrc: Tracked<FractionalResource<usize, 2>>) -> JoinHandle<()>
    requires
        aself.inv(),
        thread_rsrc@.valid(aself.invariant@.constant().thread_rsrc_ids[thread_idx], 1),
        thread_rsrc@.val() == 0,
        thread_idx == 0 || thread_idx == 1,
    {

        let sself = aself.clone();

        let handle = spawn(move || {
            let main = &*sself;
            let open_invariant_credit = create_open_invariant_credit();
            let cb: Tracked<MainIncrementCB> = Tracked( MainIncrementCB{
                    thread_idx,
                    thread_rsrc: thread_rsrc.get(),
                    invariant: &main.invariant,
                    credit: open_invariant_credit.get() } );
            let thread_rsrc = main.incrementer.increment(cb);

            let open_invariant_credit = create_open_invariant_credit();
            let cb: Tracked<MainIncrementCB>  = Tracked( MainIncrementCB{
                    thread_idx,
                    thread_rsrc: thread_rsrc.get(),
                    invariant: &main.invariant,
                    credit: open_invariant_credit.get() } );
            let thread_rsrc = main.incrementer.increment(cb);


            // Doing this again should fail verification ... and it does!
//             let open_invariant_credit = create_open_invariant_credit();
//             let cb: Tracked<MainIncrementCB>  = Tracked( MainIncrementCB{
//                     thread_idx,
//                     thread_rsrc: thread_rsrc.get(),
//                     invariant: &main.invariant,
//                     credit: open_invariant_credit.get() } );
//             assert( cb@.inv() );
//             let thread_rsrc = main.incrementer.increment(cb);
        });
        handle
    }
}

struct MainIncrementCB<'a> {
    thread_idx: usize,
    thread_rsrc: FractionalResource<usize, 2>,
    invariant: &'a Tracked<AtomicInvariant<MainInvK, MainInvV, MainInvPred>>,
    tracked credit: OpenInvariantCredit,
}

impl<'a> AtomicIncrementerIncrementCallback for MainIncrementCB<'a> {
    type CBResult = FractionalResource<usize, 2>;

    spec fn inv(&self) -> bool
    {
        &&& (self.thread_idx == 0 || self.thread_idx == 1)
        &&& self.thread_rsrc.inv()
        &&& self.thread_rsrc.id()
            == self.invariant@.constant().thread_rsrc_ids[self.thread_idx]
        &&& self.thread_rsrc.frac() == 1

        &&& self.thread_rsrc.val() < 2
    }

    spec fn id(&self) -> int
    {
        self.invariant@.constant().down_id
    }

    spec fn inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn post(&self, result: &Self::CBResult) -> bool
    {
        &&& result.valid(self.thread_rsrc.id(), 1)
        &&& result.val() == self.thread_rsrc.val() + 1
    }

    proof fn increment_cb(tracked self, tracked rsrc: &mut FractionalResource<usize, 2>) -> (tracked out: Self::CBResult)
    {
        let tracked mut thread_rsrc;
        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inv_v => {
            rsrc.combine_mut(inv_v.down_frac);
            assume( rsrc.val() + 1 <= usize::MAX );
            let new_incrementer_v = (rsrc.val() + 1) as usize;
            rsrc.update_mut(new_incrementer_v);

            assert( self.invariant@.constant().thread_rsrc_ids.contains_key(self.thread_idx) ); // trigger quantifier
            let tracked mut thread_rsrc_b = inv_v.thread_rsrcs.tracked_remove(self.thread_idx);
            thread_rsrc_b.combine_mut(self.thread_rsrc);
            let new_thread_v = (self.thread_rsrc.val() + 1) as usize;
            thread_rsrc_b.update_mut(new_thread_v);

            inv_v.down_frac = rsrc.split_mut(1);
            thread_rsrc = thread_rsrc_b.split_mut(1);
            inv_v.thread_rsrcs.tracked_insert(self.thread_idx, thread_rsrc_b);
        });
        thread_rsrc
    }
}

fn main()
{
    let (main, left_rsrc, right_rsrc) = Main::new();
    assert( main.incrementer.inv() );
    let arc_main = Arc::new(main);

    let h0 = Main::spawn(&arc_main, 0, left_rsrc);
    let h1 = Main::spawn(&arc_main, 1, right_rsrc);

    h0.join();
    h1.join();
}

} // verus
