use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::modes::*;
mod frac;
use crate::frac::*;

verus!{

struct AtomicIncrementer {
    log: SillyLog,
    caller_frac: Tracked<FractionalResource<Seq<usize>, 2>>,
}

struct AtomicIncrementerIncrementCB {
    caller_frac: FractionalResource<Seq<usize>, 2>,
}

impl SillyLogInvCallback for AtomicIncrementerIncrementCB {
    spec fn pushed_value(&self) -> usize { 1 }

    spec fn id(&self) -> int { self.caller_frac.id() }

    spec fn inv(&self) -> bool
    {
        &&& self.caller_frac.inv()
        &&& self.caller_frac.frac() == 1
    }

    proof fn append_cb(tracked self, tracked rsrc: &mut FractionalResource<Seq<usize>, 2>) -> tracked Self::CBResult
    {
        rsrc.combine_mut(self.caller_frac);

        let new_v = rsrc.val().push(1);
        rsrc.update_mut(new_v);

        let tracked caller_frac = rsrc.split_mut(1);
        caller_frac
    }

    type CBResult = FractionalResource<Seq<usize>, 2>;

    spec fn post(&self, result: &Self::CBResult) -> bool
    {
        &&& result.id() == self.id()
        &&& result.inv()
        &&& result.frac() == 1
        &&& result.val() == self.caller_frac.val().push(1)
    }
}

impl AtomicIncrementer {
    fn new() -> (out: Self)
    ensures
        out.inv()
    {
        let (log, caller_frac) = SillyLog::new();
        AtomicIncrementer{ log, caller_frac }
    }

    spec fn inv(&self) -> bool
    {
        &&& self.caller_frac@.inv()
        &&& self.caller_frac@.frac() == 1
        &&& self.caller_frac@.id() == self.log.id()
//         &&& self.caller_frac@.val().len() <= usize::MAX
    }

    spec fn val(&self) -> usize
    {
        self.caller_frac@.val().len() as usize
    }

    fn increment(&mut self)
    requires
        old(self).inv(),
    ensures
        self.val() == old(self).val() + 1,
    {
        let ghost old_self_val = self.val();

        let mut cb: Tracked<AtomicIncrementerIncrementCB> = Tracked({
            let tracked mut local_frac = FractionalResource::default();
            tracked_swap(self.caller_frac.borrow_mut(), &mut local_frac);
            AtomicIncrementerIncrementCB{caller_frac: local_frac}
        });

        let ghost pre_cb = cb@;

        self.caller_frac = self.log.append(1, cb);

        assume( pre_cb.caller_frac.val().len() < 100 ); // TODO avoid physical sie clipping issues with long log
    }
    
    fn get(&self) -> (out: usize)
    ensures
        out == self.val(),
    {
        let snapshot = self.log.read();

        assert( snapshot@ == self.caller_frac@.val() ) by {
            // TODO left off  -- need to plumb our half-frac down to
            // SillyLog so it can ensures something about read result.
            assume( false );
        }
        snapshot.len()
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

trait SillyLogInvCallback: Sized {
    type CBResult;

    spec fn pushed_value(&self) -> usize
        ;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn post(&self, result: &Self::CBResult) -> bool
        ;

    proof fn append_cb(tracked self, tracked rsrc: &mut FractionalResource<Seq<usize>, 2>) -> (tracked out: Self::CBResult)
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

    fn append<CB: SillyLogInvCallback>(&self, v: usize, cb: Tracked<CB>)
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
        let cb_result = Tracked({ cb.get().append_cb(state.abs.borrow_mut()) });
        lock_handle.release_write(state);
        cb_result
    }

    fn read(&self) -> (out: Vec<usize>)
    {
        let read_handle = self.locked_state.acquire_read();
        let result = read_handle.borrow().phy.clone();
        read_handle.release_read();
        result
    }
}

} // verus

fn main()
{
}
