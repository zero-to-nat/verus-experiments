use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::modes::*;
use vstd::invariant::*;
use std::sync::Arc;
use vstd::thread::*;

mod frac;
use crate::frac::*;

verus!{

type ID = int;

trait CallBackSemantics : Sized{
    type Param;  // input of call back (ghost resource)
    type Result; // output of call back (e.g. fractional resource)
    type ExecResult;

    spec fn _requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    ;

    spec fn _ensures(id: ID, p: Self::Param, e: Self::Result) -> bool
    ;
}

trait GenericCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn _inv(&self) -> bool
        ;

    spec fn _id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn _inv_namespace(&self) -> int
        ;

    spec fn _other_namespace(&self) -> int
        ;

    spec fn _result_post(&self, r: S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: S::ExecResult)
        -> (tracked out: (S::Result, Self::CBResult))
    requires
        self._inv(),
        S::_requires(self._id(), p, e),
    ensures
        S::_ensures(self._id(), p, out.0),
        self._result_post(e, &out.1),
    opens_invariants [ self._inv_namespace(), self._other_namespace() ]
    ;
}

struct SillyLogAppendSemantics{}

impl CallBackSemantics for SillyLogAppendSemantics  {
    type Param = FractionalResource<Seq<usize>, 2>;
    type Result = FractionalResource<Seq<usize>, 2>;
    type ExecResult = ();

    spec fn _requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    {
        p.valid(id, 1)
    }

    spec fn _ensures(id: ID, p: Self::Param, r: Self::Result) -> bool
    {
        &&& r.valid(id, 1)
        &&& r.val() == p.val().push(1)
    }
}

impl<'a, UpCB: AtomicIncrementerIncrementCallback> GenericCallBack<SillyLogAppendSemantics> for AtomicIncrementerIncrementCB<'a, UpCB> {
    type CBResult = UpCB::CBResult;

    spec fn _id(&self) -> int {
        self.invariant@.constant().down_id
    }

    spec fn _inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn _other_namespace(&self) -> int { self.up_cb.inv_namespace() }

    spec fn _inv(&self) -> bool
    {
        &&& self.up_cb.inv()
        &&& self.invariant@.constant().up_id == self.up_cb.id()
        &&& self.up_cb.inv_namespace() != self._inv_namespace()
    }

    proof fn cb(
        tracked self,
        tracked rsrc: FractionalResource<Seq<usize>, 2>,
        e: (),
    )
    -> (tracked out: (FractionalResource<Seq<usize>, 2>, Self::CBResult))
    {
        let tracked mut cb_result;
        let tracked mut new_rsrc;

        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inner_val => {
            new_rsrc = rsrc;
            new_rsrc.combine_mut(inner_val.down_frac);
            let new_v = rsrc.val().push(1);
            new_rsrc.update_mut(new_v);
            assert( self.invariant@.namespace() != self.up_cb.inv_namespace() );
            cb_result = self.up_cb.increment_cb(&mut inner_val.up_frac);
            inner_val.down_frac = new_rsrc.split_mut(1);
        });

        (new_rsrc, cb_result)
    }

    spec fn _result_post(&self, r: (), result: &Self::CBResult) -> bool
    {
        &&& self.up_cb.post(result)
    }
}

struct SillyLogReadSemantics<'a> {
    _p: &'a std::marker::PhantomData<int>,
}

impl<'a> CallBackSemantics for SillyLogReadSemantics<'a>  {
    type Param = &'a FractionalResource<Seq<usize>, 2>;
    type ExecResult = &'a Vec<usize>;
    type Result = (); 

    spec fn _requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    {
        &&& p.valid(id, 1)
        &&& p.val() == e@
    }

    spec fn _ensures(id: ID, p: Self::Param, r: Self::Result) -> bool
    {
        true
    }
}

impl<'a, UpCB: AtomicIncrementerGetCallback> GenericCallBack<SillyLogReadSemantics<'a>> for AtomicIncrementerGetCB<'a, UpCB> {
    type CBResult = UpCB::CBResult;

    spec fn _id(&self) -> int {
        self.invariant@.constant().down_id
    }

    spec fn _inv_namespace(&self) -> int { self.invariant@.namespace() }

    spec fn _other_namespace(&self) -> int { self.up_cb.inv_namespace() }

    spec fn _inv(&self) -> bool
    {
        &&& self.up_cb.inv()
        &&& self.invariant@.constant().up_id == self.up_cb.id()
        &&& self.up_cb.inv_namespace() != self._inv_namespace()
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
            cb_result = self.up_cb.get_cb(/* missing credit*/ &mut inner_val.up_frac, return_val.len());
        });

        ((), cb_result)
    }

    // result post want the value 
    spec fn _result_post(&self, return_val: &Vec<usize>, result: &Self::CBResult) -> bool
    {
        self.up_cb.post(return_val.len(), *result)
    }
}

trait SillyLogReadCallback: Sized {
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, return_val: &Vec<usize>, result: &Self::CBResult) -> bool
        ;

    proof fn read_cb(
        tracked self,
        tracked rsrc: &FractionalResource<Seq<usize>, 2>,
        return_val: &Vec<usize>)
    -> (tracked out: Self::CBResult)
    requires
        self.inv(),
        rsrc.valid(self.id(), 1),
        rsrc.val() == return_val@,
    ensures
        self.post(return_val, &out),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
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
        cb@._inv(),
        cb@._id() == self.id(),
    ensures
        cb@._result_post((), &out@),
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost old_state = state.rsrc@.val();
        state.phy.push(v);

        let tracked (new_state_rsrc, cb_result) = ( cb.get().cb(state.rsrc.get(), ()) );
        state.rsrc = Tracked(new_state_rsrc);

        lock_handle.release_write(state);
        Tracked(cb_result)
    }

    fn read<CB: SillyLogReadCallback>(&self, cb: Tracked<CB>)
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

        let cbresult = Tracked({ cb.get().read_cb(&callee_frac.borrow(), &phy_result) });
        read_handle.release_read();

        (phy_result, cbresult)
    }
}

//////////////////////////////////////////////////////////////////////////////

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
        self.inv(),
        old(rsrc).valid(self.id(), 1),
    ensures
        rsrc.valid(self.id(), 1),
        rsrc.val() == old(rsrc).val() + 1,
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

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, return_val: usize, result: Self::CBResult) -> bool
        ;

    proof fn get_cb(tracked self, tracked rsrc: &FractionalResource<usize, 2>, return_val: usize) -> (tracked out: Self::CBResult)
    requires
        self.inv(),
        rsrc.valid(self.id(), 1),
        return_val == rsrc.val(),
    ensures
        self.post(return_val, out),
    opens_invariants [ self.inv_namespace() ]
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
        &&& v.up_frac.valid(k.up_id, 1)
        &&& v.up_frac.val() == v.down_frac.val().len()
        &&& v.down_frac.valid(k.down_id, 1)
    }
}

struct AtomicIncrementerIncrementCB<'a, UpCB: AtomicIncrementerIncrementCallback> {
    invariant: &'a Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    up_cb: UpCB,
    tracked credit: OpenInvariantCredit,
}


struct AtomicIncrementerGetCB<'a, UpCB: AtomicIncrementerGetCallback> {
    invariant: &'a Tracked<AtomicInvariant<AtomicIncrementerInvK, AtomicIncrementerInvV, AtomicIncrementerInvPred>>,
    up_cb: UpCB,
    tracked credit: OpenInvariantCredit,
}

impl<'a, UpCB: AtomicIncrementerGetCallback> SillyLogReadCallback for AtomicIncrementerGetCB<'a, UpCB> {
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

        assert( down_cb@._inv() );
        self.log.append(1, down_cb)
    }
    
    fn get<CB: AtomicIncrementerGetCallback>(&self, up_cb: Tracked<CB>)
    -> (out: (usize, Tracked<CB::CBResult>))
    requires
        self.inv(),
        up_cb@.inv(),
        up_cb@.id() == self.id(),
        up_cb@.inv_namespace() != self.inv_namespace(),
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

impl<'a> AtomicIncrementerIncrementCallback for MainIncrementCB<'a> {
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

struct MainGetCB<'a> {
    invariant: &'a Tracked<AtomicInvariant<MainInvK, MainInvV, MainInvPred>>,
    tracked credit: OpenInvariantCredit,
}

impl<'a> AtomicIncrementerGetCallback for MainGetCB<'a> {
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

    spec fn post(&self, result_val: usize, result: Self::CBResult) -> bool
    {
        &&& result_val <= 4
    }

    proof fn get_cb(tracked self, tracked rsrc: &FractionalResource<usize, 2>, return_val: usize) -> (tracked out: Self::CBResult)
    {
        open_atomic_invariant!(self.credit => &self.invariant.borrow() => inv_v => {
            inv_v.down_frac.agree(rsrc);

            assert( self.invariant@.constant().thread_rsrc_ids.contains_key(0) );   // trigger
            assert( self.invariant@.constant().thread_rsrc_ids.contains_key(1) );   // trigger
        });
        ()
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
