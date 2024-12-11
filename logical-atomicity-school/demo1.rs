use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::modes::*;
mod frac;
use crate::frac::*;

verus!{

struct AtomicIncrementer {
    log: SillyLog,
    caller_frac: Tracked<FractionalResource<Seq<i64>, 2>>,
}

struct AtomicIncrementerIncrementCB {
    caller_frac: FractionalResource<Seq<i64>, 2>,
}

impl SillyLogInvCallback for AtomicIncrementerIncrementCB {
    spec fn pushed_value(&self) -> i64 { 1 }

    spec fn id(&self) -> int { self.caller_frac.id() }

    spec fn inv(&self) -> bool
    {
        &&& self.caller_frac.inv()
        &&& self.caller_frac.frac() == 1
    }

    proof fn append_cb(tracked &mut self, tracked rsrc: &mut FractionalResource<Seq<i64>, 2>)
    {
        let tracked mut local_frac = FractionalResource::default();
        tracked_swap(&mut self.caller_frac, &mut local_frac);

        rsrc.combine_mut(local_frac);

        let new_v = rsrc.val().push(1);
        rsrc.update_mut(new_v);

        self.caller_frac = rsrc.split_mut(1);
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
    }

    fn increment(&mut self)
    requires
        old(self).inv(),
    {
        let mut cb: Tracked<AtomicIncrementerIncrementCB> = Tracked({
            let tracked mut local_frac = FractionalResource::default();
            tracked_swap(self.caller_frac.borrow_mut(), &mut local_frac);
            AtomicIncrementerIncrementCB{caller_frac: local_frac}
        });

        assert( cb@.caller_frac.inv() );
        self.log.append(1, &mut cb);
        self.caller_frac = Tracked(cb.get().caller_frac);
    }
    
    fn get(&self) -> i64
    {
        let snapshot = self.log.read();
        snapshot.len() as i64
    }
}

//////////////////////////////////////////////////////////////////////////////

struct SillyLogState {
    phy: Vec<i64>,
    abs: Tracked<FractionalResource<Seq<i64>, 2>>,
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
    spec fn pushed_value(&self) -> i64
        ;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    proof fn append_cb(tracked &mut self, tracked rsrc: &mut FractionalResource<Seq<i64>, 2>)
    requires
        old(rsrc).frac() == 1,
        old(rsrc).inv(),
        old(self).inv(),
        old(self).id() == old(rsrc).id()
    ensures
        rsrc.frac() == 1,
        rsrc.inv(),
        rsrc.val() == old(rsrc).val().push(old(self).pushed_value()),
        // stupid stuff that makes us sad
        self.id() == old(self).id(),
        rsrc.id() == old(rsrc).id(),
    ;
}

impl SillyLog {
    spec fn id(&self) -> int { self.locked_state.pred().id }

    fn new() -> (out: (Self, Tracked<FractionalResource<Seq<i64>, 2>>))
    ensures
        out.1@.val() == Seq::<i64>::empty(),
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

    fn append<CB: SillyLogInvCallback>(&self, v: i64, cb: &mut Tracked<CB>)
    requires
        old(cb)@.pushed_value() == v,
        old(cb)@.inv(),
        old(cb)@.id() == self.id(),
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost old_state = state.abs@.val();
        state.phy.push(v);
        proof {
            cb.borrow_mut().append_cb(state.abs.borrow_mut());
        }
        assert( self.locked_state.pred().inv(state) );
        lock_handle.release_write(state);
    }

    fn read(&self) -> Vec<i64>
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
