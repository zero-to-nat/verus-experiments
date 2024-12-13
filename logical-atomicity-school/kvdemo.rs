use builtin::*;

use vstd::prelude::*;
use vstd::rwlock::*;
use std::collections::hash_map::*;
use vstd::std_specs::hash::*;
// use vstd::modes::*;
use vstd::invariant::*;
use std::sync::Arc;
use vstd::thread::*;

mod frac;
use crate::frac::*;

verus!{
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub type Key = u64; // NOTE: usize doesn't implement key model, not reasonable
pub type Value = usize;

struct KVState {
    phy: HashMap<Key, Value>,
    rsrc_map: Tracked<Map<Key, FractionalResource<Value, 2>>>,
}

struct KVPred {
    key_rsrc_ids: Map<Key, int>,
}

impl RwLockPredicate<KVState> for KVPred {
    closed spec fn inv(self, v: KVState) -> bool {
        &&& self.key_rsrc_ids.dom() == v.rsrc_map@.dom()
        &&& self.key_rsrc_ids.dom() == v.phy@.dom()
        &&& forall |k| #[trigger] self.key_rsrc_ids.contains_key(k)
            ==> {
                &&& v.rsrc_map@[k].valid(self.key_rsrc_ids[k], 1)
                &&& v.rsrc_map@[k].val() == v.phy@[k]
            }
    }
}

struct KVStore{
    locked_state: RwLock<KVState, KVPred>,
}

trait KVStoreGetCallBack: Sized{
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, return_val: usize, result: Self::CBResult) -> bool
        ;

    proof fn get_cb(tracked self, tracked rsrc: &FractionalResource<usize, 2>, return_val: Value) 
        -> (tracked out: Self::CBResult)
    requires
        self.inv(),
        rsrc.valid(self.id(), 1),
        return_val == rsrc.val(),
    ensures
        self.post(return_val, out),
    opens_invariants [ self.inv_namespace() ]
    ;
}

trait KVStoreSetCallBack: Sized{
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, set_val: Value, result: Self::CBResult) -> bool
        ;

    proof fn set_cb(tracked self, tracked rsrc: FractionalResource<Value, 2>, set_val: Value) 
        -> (tracked out: (FractionalResource<Value, 2>, Self::CBResult))
    requires
        self.inv(),
        rsrc.valid(self.id(), 1),
    ensures
        out.0.valid(self.id(), 1),
        out.0.val() == set_val,
        self.post(set_val, out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

impl KVStore {
    spec fn ids(&self) -> Map<Key, int>
    {
        self.locked_state.pred().key_rsrc_ids
    }

    // dynamic create should just give a default value
    // TODO: take in a hashmap and populate
    fn new(init_key: Key, init_value: Value) -> (out: (Self, Tracked<FractionalResource<Value, 2>>))
        ensures
            out.0.ids().contains_key(init_key),
            out.1@.valid(out.0.ids()[init_key], 1),
            out.1@.val() == init_value,
    {
        let mut phy = HashMap::new();
        phy.insert(init_key, init_value);
        let tracked(my_frac, out_frac) = FractionalResource::new(init_value).split(1);

        let tracked rsrc_map = Map::tracked_empty();
        proof { rsrc_map.tracked_insert(init_key, my_frac); }
        let state = KVState{phy, rsrc_map: Tracked(rsrc_map)};

        let ghost pred = KVPred{key_rsrc_ids: map![init_key => out_frac.id()]};
        let locked_state = RwLock::new(state, Ghost(pred));

        (KVStore{locked_state}, Tracked(out_frac))
    }

    fn get<CB: KVStoreGetCallBack>(&self, k: Key, cb: Tracked<CB>) 
        -> (out: (Value, Tracked<CB::CBResult>))
        requires    
            // NOTE: need to remove when allowing for concurrent create & delete bc we won't 
            // have the knowledge prior to calling this function
            self.ids().contains_key(k), 
            cb@.inv(),
            cb@.id() == self.ids()[k],
        ensures 
            cb@.post(out.0, out.1@),
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let phy_result_ref = state.phy.get(&k);
        assert(phy_result_ref is Some);
        let phy_result = *phy_result_ref.unwrap();

        let tracked callee_frac = state.rsrc_map.borrow().tracked_borrow(k);
        let cbresult = Tracked({ cb.get().get_cb(callee_frac, phy_result) });

        read_handle.release_read();
        (phy_result, cbresult)
    }

    fn set<CB: KVStoreSetCallBack>(&self, k: Key, v: Value, cb: Tracked<CB>) 
        -> (out: Tracked<CB::CBResult>)
    requires
        self.ids().contains_key(k), 
        cb@.inv(),
        cb@.id() == self.ids()[k],
    ensures 
        cb@.post(v, out@),
    {   
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost old_phy = state.phy@;

        let tracked my_frac = state.rsrc_map.borrow_mut().tracked_remove(k);
        state.phy.insert(k, v);

        let tracked (my_frac, cb_result) = ( cb.get().set_cb(my_frac, v) );
        proof{ state.rsrc_map.borrow_mut().tracked_insert(k, my_frac); }

        assert(old_phy.dom() =~= state.phy@.dom());
        lock_handle.release_write(state);
        Tracked(cb_result)
    }
}

// sequential client

struct SequentialKey<'a>{
    store: &'a KVStore,
    k: Key,
    r: Tracked<FractionalResource<Value, 2>>,
}

impl<'a> SequentialKey<'a>{
    spec fn view(&self) -> Value
    {
        self.r@.val()
    }

    spec fn inv(&self) -> bool
    {
        &&& self.store.ids().contains_key(self.k)
        &&& self.r@.valid(self.store.ids()[self.k], 1)
    }

    fn get(&self) -> (out: Value)
        requires self.inv()
        ensures out == self@
    {
        // NOTE: type 
        let cb: Tracked<SequentialGetCB> = Tracked(SequentialGetCB{rsrc: &self}); 
        let (v, _) = self.store.get(self.k, cb);
        v
    }

    fn set(&mut self, set_val: Value) 
        requires old(self).inv()
        ensures 
            self@ == set_val,
            self.inv()
    {
        let tracked frac = self.r.borrow_mut().take();
        let cb: Tracked<SequentialSetCB> = Tracked(SequentialSetCB{rsrc: frac}); 
        self.r = self.store.set(self.k, set_val, cb);
    }
}

struct SequentialGetCB<'a>{
    rsrc: &'a SequentialKey<'a>,
}

impl<'a> KVStoreGetCallBack for SequentialGetCB<'a> {
    type CBResult = ();
    
    spec fn inv(&self) -> bool
    {
        self.rsrc.r@.inv()
    }

    spec fn id(&self) -> int
    {
        self.rsrc.r@.id()
    }

    spec fn inv_namespace(&self) -> int
    {
        arbitrary() // not used in sequential case
    }

    spec fn post(&self, return_val: usize, result: Self::CBResult) -> bool
    {
        return_val == self.rsrc@
    }

    proof fn get_cb(tracked self, tracked rsrc: &FractionalResource<usize, 2>, return_val: Value) 
        -> (tracked out: Self::CBResult)
    {
        rsrc.agree(self.rsrc.r.borrow());
        ()
    }
}

struct SequentialSetCB{
    rsrc: FractionalResource<Value, 2>,
}

impl KVStoreSetCallBack for SequentialSetCB {
    type CBResult = FractionalResource<Value, 2>;
    
    spec fn inv(&self) -> bool
    {
        self.rsrc.valid(self.id(), 1)
    }

    spec fn id(&self) -> int
    {
        self.rsrc.id()
    }

    spec fn inv_namespace(&self) -> int
    {
        arbitrary() // not used in sequential case
    }

    spec fn post(&self, set_val: Value, result: Self::CBResult) -> bool
    {
        &&& result.val() == set_val
        &&& result.valid(self.id(), 1)
    }

    proof fn set_cb(tracked self, tracked rsrc: FractionalResource<Value, 2>, set_val: Value) 
    -> (tracked out: (FractionalResource<Value, 2>, Self::CBResult))
    {
        let tracked mut new_rsrc = rsrc.combine(self.rsrc);
        new_rsrc.update_mut(set_val);
        let tracked my_part = new_rsrc.split_mut(1);
        (my_part, new_rsrc)
    }
}

// assert client's inv being good
// sequential put & threads
// atomic inv 5 or 6

fn main() {
    let (store, init_frac) = KVStore::new(0, 1);
    let mut seq_key = SequentialKey{store: &store, k: 0, r: init_frac}; 

    let v = seq_key.get();
    assert(v == 1);

    seq_key.set(2);
    let v = seq_key.get();
    assert(v == 2);
}

}