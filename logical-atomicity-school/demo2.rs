use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use std::sync::Arc;
use vstd::thread::*;

mod frac;
use crate::frac::*;

verus!{

type ID = int;

trait CallBackSemantics : Sized{
    type Param;         // input of call back (ghost resource)
    type GhostResult;   // output of call back (e.g. fractional resource)
    type ExecResult;

    spec fn requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    ;

    spec fn ensures(id: ID, p: Self::Param, e: Self::GhostResult) -> bool
    ;
}

trait GenericCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), p, *e),
    ensures
        S::ensures(self.id(), p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

// NOTE: the only difference is the param type in the callback proof fn
// this is needed to untie the lifetime of the param from the callback struct
trait GenericReadCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: &S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), *p, *e),
    ensures
        S::ensures(self.id(), *p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

// NOTE: a workaround for opens_invariants not taking a set of namespaces
// does not open other_namespace
trait GenericSingleInvCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), p, *e),
    ensures
        S::ensures(self.id(), p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

// NOTE: the only difference is the param type in the callback proof fn
// this is needed to untie the lifetime of the param from the callback struct
trait GenericSingleInvReadCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: &S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), *p, *e),
    ensures
        S::ensures(self.id(), *p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

////////////////////////////////////////////////////////////////////////////

struct SillyLogAppendSemantics{}

impl CallBackSemantics for SillyLogAppendSemantics  {
    type Param = FractionalResource<Seq<usize>, 2>;
    type GhostResult = FractionalResource<Seq<usize>, 2>;
    type ExecResult = ();

    spec fn requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    {
        p.valid(id, 1)
    }

    spec fn ensures(id: ID, p: Self::Param, r: Self::GhostResult) -> bool
    {
        &&& r.valid(id, 1)
        &&& r.val() == p.val().push(1)
    }
}

impl<'a, UpCB: GenericSingleInvCallBack<AtomicIncIncrementSemantics>> GenericCallBack<SillyLogAppendSemantics> for AtomicIncrementerIncrementCB<'a, UpCB> {
    type CBResult = UpCB::CBResult;

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

    proof fn cb(
        tracked self,
        tracked rsrc: FractionalResource<Seq<usize>, 2>,
        e: &(),
    )
    -> (tracked out: (FractionalResource<Seq<usize>, 2>, Self::CBResult))
    {
        let tracked mut new_rsrc;
        let tracked mut cb_result;

        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inner_val => {
            new_rsrc = rsrc;
            new_rsrc.combine_mut(inner_val.down_frac);
            let new_v = rsrc.val().push(1);
            new_rsrc.update_mut(new_v);
            assert( self.invariant@.namespace() != self.up_cb.inv_namespace() );

            let tracked (new_up_frac, result) = self.up_cb.cb(inner_val.up_frac.take(), &());
            inner_val.up_frac = new_up_frac;
            inner_val.down_frac = new_rsrc.split_mut(1);
            cb_result = result;
        });

        (new_rsrc, cb_result)
    }

    spec fn post(&self, r: &(), result: &Self::CBResult) -> bool
    {
        &&& self.up_cb.post(r, result)
    }
}

struct SillyLogReadSemantics {}

impl CallBackSemantics for SillyLogReadSemantics {
    type Param = FractionalResource<Seq<usize>, 2>;
    type ExecResult = Vec<usize>;
    type GhostResult = ();

    spec fn requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    {
        &&& p.valid(id, 1)
        &&& p.val() == e@
    }

    spec fn ensures(id: ID, p: Self::Param, r: Self::GhostResult) -> bool
    {
        true
    }
}

impl<'a, UpCB: GenericSingleInvReadCallBack<AtomicIncGetSemantics>> GenericReadCallBack<SillyLogReadSemantics> for AtomicIncrementerGetCB<'a, UpCB> {
    type CBResult = UpCB::CBResult;

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

    proof fn cb(
        tracked self,
        tracked rsrc: &FractionalResource<Seq<usize>, 2>,
        return_val: &Vec<usize>)
    -> (tracked out: ((), Self::CBResult))
    {
        let tracked mut cb_result;
        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inner_val => {
            inner_val.down_frac.agree(rsrc);
            let tracked(a, b) = self.up_cb.cb(/* missing credit*/ &mut inner_val.up_frac, &return_val.len());
            cb_result = b;
        });

        ((), cb_result)
    }

    // result post want the value 
    spec fn post(&self, return_val: &Vec<usize>, result: &Self::CBResult) -> bool
    {
        self.up_cb.post(&return_val.len(), result)
    }
}

struct SillyLogState {
    phy: Vec<usize>,
    rsrc: Tracked<FractionalResource<Seq<usize>, 2>>,
}

struct SillyLogPred {
    id: int,
}

impl RwLockPredicate<SillyLogState> for SillyLogPred {
    closed spec fn inv(self, v: SillyLogState) -> bool {
        &&& v.rsrc@.valid(self.id, 1) 
        &&& v.rsrc@.val() == v.phy@
    }
}

struct SillyLog {
    locked_state: RwLock<SillyLogState, SillyLogPred>,
}

impl SillyLog {
    spec fn id(&self) -> int { self.locked_state.pred().id }

    fn new() -> (out: (Self, Tracked<FractionalResource<Seq<usize>, 2>>))
    ensures
        out.1@.valid(out.0.id(), 1),
        out.1@.val() == Seq::<usize>::empty(),
    {
        let tracked(my_part, caller_part) = FractionalResource::new(Seq::empty()).split(1);
        let state = SillyLogState {
            phy: Vec::new(),
            rsrc: Tracked(my_part),
        };
        let ghost pred = SillyLogPred{id: state.rsrc@.id()};
        let locked_state = RwLock::new(state, Ghost(pred));
        let log = Self{ locked_state };
        (log, Tracked(caller_part))
    }

    fn append<CB: GenericCallBack<SillyLogAppendSemantics>>(&self, v: usize, cb: Tracked<CB>)
        -> (out: Tracked<CB::CBResult>)
    requires
        v == 1,
        cb@.inv(),
        cb@.id() == self.id(),
    ensures
        cb@.post(&(), &out@),
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost old_state = state.rsrc@.val();
        state.phy.push(v);

        let tracked (new_state_rsrc, cb_result) = ( cb.get().cb(state.rsrc.get(), &()) );
        state.rsrc = Tracked(new_state_rsrc);

        lock_handle.release_write(state);
        Tracked(cb_result)
    }

    fn read<CB: GenericReadCallBack<SillyLogReadSemantics>>(&self, cb: Tracked<CB>)
    -> (out: (Vec<usize>, Tracked<CB::CBResult>))
    requires
        cb@.inv(),
        cb@.id() == self.id(),
    ensures
        cb@.post(&out.0, &out.1@),
    {
        let read_handle = self.locked_state.acquire_read();
        let phy_result = read_handle.borrow().phy.clone();
        let callee_frac = &read_handle.borrow().rsrc;
        let tracked (_, cb_result) = ( cb.get().cb(&callee_frac.borrow(), &phy_result) );
        read_handle.release_read();

        (phy_result, Tracked(cb_result))
    }
}

//////////////////////////////////////////////////////////////////////////////

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
        &&& v.up_frac.valid(k.up_id, 1)
        &&& v.up_frac.val() == v.down_frac.val().len()
        &&& v.down_frac.valid(k.down_id, 1)
    }
}

struct AtomicIncrementerIncrementCB<'a, UpCB: GenericSingleInvCallBack<AtomicIncIncrementSemantics>> {
    invariant: &'a Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    up_cb: UpCB,
    tracked credit: OpenInvariantCredit,
}

struct AtomicIncrementerGetCB<'a, UpCB: GenericSingleInvReadCallBack<AtomicIncGetSemantics>> {
    invariant: &'a Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    up_cb: UpCB,
    tracked credit: OpenInvariantCredit,
}

struct AtomicIncrementer {
    invariant: Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    log: SillyLog,
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
        let tracked(up_frac, api_frac) = FractionalResource::new(0).split(1);

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

    fn increment<CB: GenericSingleInvCallBack<AtomicIncIncrementSemantics>>(&self, up_cb: Tracked<CB>)
        -> (out: Tracked<CB::CBResult>)
    requires
        self.inv(),
        up_cb@.inv(),
        up_cb@.id() == self.id(),
        up_cb@.inv_namespace() != self.inv_namespace(),
    ensures
        up_cb@.post(&(), &out@),
    {
        let open_invariant_credit = create_open_invariant_credit();
        let down_cb:Tracked<AtomicIncrementerIncrementCB<CB>> = Tracked(AtomicIncrementerIncrementCB{invariant: &self.invariant, up_cb: up_cb.get(), credit: open_invariant_credit.get() });

        assert( down_cb@.inv() );
        self.log.append(1, down_cb)
    }
    
    fn get<CB: GenericSingleInvReadCallBack<AtomicIncGetSemantics>>(&self, up_cb: Tracked<CB>)
    -> (out: (usize, Tracked<CB::CBResult>))
    requires
        self.inv(),
        up_cb@.inv(),
        up_cb@.id() == self.id(),
        up_cb@.inv_namespace() != self.inv_namespace(),
    ensures
        up_cb@.post(&out.0, &out.1@),
    {
        let open_invariant_credit = create_open_invariant_credit();
        let down_cb:Tracked<AtomicIncrementerGetCB<CB>> = Tracked(AtomicIncrementerGetCB{invariant: &self.invariant, up_cb: up_cb.get(), credit: open_invariant_credit.get()});

        let (down_return_val, down_cb_result) = self.log.read(down_cb);
        (down_return_val.len(), down_cb_result)
    }
}

//////////////////////////////////////////////////////////////////////////////


struct MainInvK {
    down_id: int,
    thread_rsrc_ids: Map<usize, int>,
}

struct MainInvV {
    down_frac: FractionalResource<usize, 2>,
    thread_rsrcs: Map<usize, FractionalResource<usize, 2>>, // main's client rsrc for thread 
}

struct MainInvPred {}

impl InvariantPredicate<MainInvK, MainInvV> for MainInvPred {
    closed spec fn inv(k: MainInvK, v: MainInvV) -> bool
    {
        &&& v.down_frac.valid(k.down_id, 1)

        &&& forall |idx| #[trigger] k.thread_rsrc_ids.contains_key(idx) ==> {
            &&& v.thread_rsrcs[idx].valid(k.thread_rsrc_ids[idx], 1)
            &&& v.thread_rsrcs[idx].val() <= 2
        }

        // there are exactly two threads
        &&& k.thread_rsrc_ids.dom() == set![ 0usize, 1usize ]
        &&& v.thread_rsrcs.dom() == k.thread_rsrc_ids.dom()

        &&& v.down_frac.val() == v.thread_rsrcs[0].val() + v.thread_rsrcs[1].val()
    }
}

struct MainIncrementCB<'a> {
    thread_idx: usize,
    thread_rsrc: FractionalResource<usize, 2>,
    invariant: &'a Tracked<AtomicInvariant<MainInvK, MainInvV, MainInvPred>>,
    tracked credit: OpenInvariantCredit,
}

struct AtomicIncIncrementSemantics{}

impl CallBackSemantics for AtomicIncIncrementSemantics{
    type Param = FractionalResource<usize, 2>;
    type GhostResult = FractionalResource<usize, 2>;
    type ExecResult = ();

    spec fn requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    {
        p.valid(id, 1)
    }

    spec fn ensures(id: ID, p: Self::Param, e: Self::GhostResult) -> bool
    {
        &&& e.valid(id, 1)
        &&& e.val() == p.val() + 1
    }
}

impl<'a> GenericSingleInvCallBack<AtomicIncIncrementSemantics> for MainIncrementCB<'a> {
    type CBResult = FractionalResource<usize, 2>;

    spec fn inv(&self) -> bool
    {
        &&& (self.thread_idx == 0 || self.thread_idx == 1)
        &&& self.thread_rsrc.valid(self.invariant@.constant().thread_rsrc_ids[self.thread_idx], 1)
        &&& self.thread_rsrc.val() < 2
    }

    spec fn id(&self) -> int
    {
        self.invariant@.constant().down_id
    }

    spec fn inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn post(&self, r: &(), cb_result: &Self::CBResult) -> bool
    {
        &&& cb_result.valid(self.thread_rsrc.id(), 1)
        &&& cb_result.val() == self.thread_rsrc.val() + 1
    }

    proof fn cb(tracked self, tracked rsrc: FractionalResource<usize, 2>, e: &()) 
        -> (tracked out: (FractionalResource<usize, 2>, Self::CBResult))
    {
        let tracked mut new_rsrc;
        let tracked mut thread_rsrc; // cb result

        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inv_v => {
            new_rsrc = rsrc;
            new_rsrc.combine_mut(inv_v.down_frac);
            assume( new_rsrc.val() + 1 <= usize::MAX );
            let new_incrementer_v = (new_rsrc.val() + 1) as usize;
            new_rsrc.update_mut(new_incrementer_v);

            assert( self.invariant@.constant().thread_rsrc_ids.contains_key(self.thread_idx) ); // trigger quantifier
            let tracked mut thread_rsrc_b = inv_v.thread_rsrcs.tracked_remove(self.thread_idx);
            thread_rsrc_b.combine_mut(self.thread_rsrc);
            let new_thread_v = (self.thread_rsrc.val() + 1) as usize;
            thread_rsrc_b.update_mut(new_thread_v);

            inv_v.down_frac = new_rsrc.split_mut(1);
            thread_rsrc = thread_rsrc_b.split_mut(1);
            inv_v.thread_rsrcs.tracked_insert(self.thread_idx, thread_rsrc_b);
        });

        (new_rsrc, thread_rsrc)
    }
}

struct MainGetCB<'a> {
    invariant: &'a Tracked<AtomicInvariant<MainInvK, MainInvV, MainInvPred>>,
    tracked credit: OpenInvariantCredit,
}

struct AtomicIncGetSemantics{}

impl CallBackSemantics for AtomicIncGetSemantics{
    type Param = FractionalResource<usize, 2>;
    type GhostResult = ();
    type ExecResult = usize;

    spec fn requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    {
        &&& p.valid(id, 1)
        &&& p.val() == e
    }

    spec fn ensures(id: ID, p: Self::Param, e: Self::GhostResult) -> bool
    {
        true
    }
}

impl<'a> GenericSingleInvReadCallBack<AtomicIncGetSemantics> for MainGetCB<'a> {
    type CBResult = ();

    spec fn inv(&self) -> bool
    {
        true
    }

    spec fn id(&self) -> int
    {
        self.invariant@.constant().down_id
    }

    spec fn inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn post(&self, result_val: &usize, result: &Self::CBResult) -> bool
    {
        result_val <= 4
    }

    proof fn cb(tracked self, tracked rsrc: &FractionalResource<usize, 2>, return_val: &usize) 
        -> (tracked out: ((), Self::CBResult))
    {
        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inv_v => {
            inv_v.down_frac.agree(rsrc);

            assert( self.invariant@.constant().thread_rsrc_ids.contains_key(0) );   // trigger
            assert( self.invariant@.constant().thread_rsrc_ids.contains_key(1) );   // trigger
        });
        ((), ())
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

        let tracked(left_inv_rsrc, left_thread_rsrc) = FractionalResource::new(0).split(1);
        let tracked(right_inv_rsrc, right_thread_rsrc) = FractionalResource::new(0).split(1);

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

    fn spawn_incrementer(aself: &Arc<Self>, thread_idx: usize, thread_rsrc: Tracked<FractionalResource<usize, 2>>) -> JoinHandle<()>
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

    fn spawn_getter(aself: &Arc<Self>) -> (handle: JoinHandle<usize>)
    requires
        aself.inv(),
    ensures
        forall|ret: usize| #[trigger] handle.predicate(ret) ==> ret <= 4
    {
        let sself = aself.clone();
        let handle = spawn(move || {
            ensures(|return_value: usize| return_value <= 4);

            let main = &*sself;

            let open_invariant_credit = create_open_invariant_credit();
            let cb: Tracked<MainGetCB> = Tracked( MainGetCB{
                    invariant: &main.invariant,
                    credit: open_invariant_credit.get() } );
            let (return_val, unit) = main.incrementer.get(cb);
            assert( return_val <= 4 );
            return_val
        });
        handle
    }
}

fn main()
{
    let (main, left_rsrc, right_rsrc) = Main::new();
    assert( main.incrementer.inv() );
    let arc_main = Arc::new(main);

    let h0 = Main::spawn_incrementer(&arc_main, 0, left_rsrc);
    let h1 = Main::spawn_incrementer(&arc_main, 1, right_rsrc);

    let h2 = Main::spawn_getter(&arc_main);

    h0.join();
    h1.join();
    let computation = h2.join();
    assert(
        match computation {
            Ok(value) => value <= 4,
            Err(()) => true,
        }
    );
}

} // verus
