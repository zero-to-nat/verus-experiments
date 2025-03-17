use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;
use crate::logatom::*;
use std::marker::PhantomData;
use vstd::rwlock::*;
use vstd::std_specs::hash::*;
use std::collections::hash_map::*;
use std::hash::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

tokenized_state_machine! {
    #[verifier::reject_recursive_types(Key)]
    KVStoreSM<Key, Value> {
        fields {
            #[sharding(variable)]
            pub inner: Map<Key, Value>,

            #[sharding(variable)]
            pub client: Map<Key, Value>
        }

        init! {
            initialize(innr: Map<Key, Value>, cl: Map<Key, Value>) 
            {
                require innr == Map::<Key, Value>::empty();
                require cl == Map::<Key, Value>::empty();

                init inner = innr;
                init client = cl;
            }
        }

        property! {
            get(k: Key, v: Option<Value>) {
                require pre.inner.contains_key(k) ==> v == Some(pre.inner[k]);
                require !pre.inner.contains_key(k) ==> v == None::<Value>;

                assert pre.client.contains_key(k) ==> v == Some(pre.client[k]) by {
                    assert(pre.inv());
                };
                assert !pre.client.contains_key(k) ==> v == None::<Value> by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            put(k: Key, v: Value, new_inner: Map<Key, Value>) {
                require new_inner == pre.inner.insert(k, v);
                
                update inner = new_inner;
                update client = new_inner;

                assert new_inner.contains_key(k) && new_inner[k] == v by {

                };
            }
        }

        property! {
            agree() {
                assert pre.client == pre.inner by {
                    assert(pre.inv());
                };
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            &&& self.inner == self.client
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, innr: Map<Key, Value>, cl: Map<Key, Value>) { }
              
        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: Key, v: Value, new_inner: Map<Key, Value>) { }
    }
}

/// get operation
pub struct KVStoreGetOperation<Key, Value> {
    pub id: InstanceId,
    pub k: Key,
    pub v: PhantomData<Value>
}

impl<Key, Value> ReadOperation for KVStoreGetOperation<Key, Value> {
    type Instance = Tracked<KVStoreSM::Instance<Key, Value>>;
    type Resource = Tracked<KVStoreSM::inner<Key, Value>>;
    type ExecResult = Option::<Value>;

    open spec fn requires(self, inst: Self::Instance, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == r@.instance_id()
        &&& r@.value().contains_key(self.k) ==> e.is_some() && r@.value()[self.k] == e.unwrap()
        &&& !r@.value().contains_key(self.k) ==> e.is_none()
    }
}

/// put operation
pub struct KVStorePutOperation<Key, Value> {
    pub id: InstanceId,
    pub k: Key,
    pub v: Value
}

impl<Key, Value> MutOperation for KVStorePutOperation<Key, Value> {
    type Instance = Tracked<KVStoreSM::Instance<Key, Value>>;
    type Resource = KVStoreSM::inner<Key, Value>;
    type ExecResult = ();
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, inst: Self::Instance, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == r.instance_id()
    }

    open spec fn ensures(self, hint: Self::ApplyHint, inst: Self::Instance, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == post.instance_id()
        &&& post.value() == pre.value().insert(self.k, self.v)
    }
}

pub open spec fn get_op<Key, Value>(id: InstanceId, k: Key) -> KVStoreGetOperation<Key, Value> {
    KVStoreGetOperation{ id: id, k: k, v: PhantomData }
}

pub open spec fn put_op<Key, Value>(id: InstanceId, k: Key, v: Value) -> KVStorePutOperation<Key, Value> {
    KVStorePutOperation{ id: id, k: k, v: v }
}

/// KVStore interface
pub trait KVStore<Key, Value> : Sized {
    spec fn id(&self) -> InstanceId;

    spec fn inv(&self) -> bool;

    spec fn new_pre() -> bool;

    /// On initialization, this store creates one fractional resource for every possible key in the map.
    /// Each key begins with an "uninitialized" value of None to represent that it is not present in the store.
    fn new() 
        -> (out: (Self, Tracked<KVStoreSM::client<Key, Value>>))
    requires
        Self::new_pre()
    ensures 
        out.0.inv(),
        out.0.id() == out.1@.instance_id(),
        out.1@.value() == Map::<Key, Value>::empty()
    ; 

    /// Returns Some if this key is in the store, returns None otherwise.
    fn get<Lin: ReadLinearizer<KVStoreGetOperation<Key, Value>>>(&self, k: Key, lin: Tracked<Lin>) 
        -> (out: (Option::<Value>, Tracked<Lin::ApplyResult>))
    requires
        self.inv(),
        lin@.pre(get_op(self.id(), k))
    ensures 
        lin@.post(get_op(self.id(), k), out.0, out.1@)
    ;

    /// Inserts the given key-value pair into the store, overwriting the old value.
    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, Value>>>(&self, k: Key, v: Value, tracked lin: &mut Lin) 
        -> (out: Tracked<Lin::ApplyResult>)
    requires
        self.inv(),
        old(lin).pre(put_op(self.id(), k, v))
    ensures
        lin.post(*old(lin), put_op(self.id(), k, v), (), out@)
    ;
}

/// KVStore implementation with single lock and hash table
#[verifier::reject_recursive_types(Key)]
struct HashKVState<Key, Value> {
    phy: HashMap<Key, Value>,
    inst: Tracked<KVStoreSM::Instance<Key, Value>>,
    inner: Tracked<KVStoreSM::inner<Key, Value>>,
}

struct KVPred {
    id: InstanceId
}

impl<Key, Value> RwLockPredicate<HashKVState<Key, Value>> for KVPred {
    closed spec fn inv(self, v: HashKVState<Key, Value>) -> bool {
        &&& v.inst@.id() == self.id
        &&& v.inner@.instance_id() == self.id
        &&& v.inner@.value() == v.phy@
    }
}

#[verifier::reject_recursive_types(Key)]
struct HashKVStore<Key, Value> {
    locked_state: RwLock<HashKVState<Key, Value>, KVPred>,
}

impl<Key: Eq + Hash> KVStore<Key, usize> for HashKVStore<Key, usize> {
    closed spec fn id(&self) -> InstanceId
    {
        self.locked_state.pred().id
    }

    open spec fn inv(&self) -> bool {
        &&& obeys_key_model::<Key>()
    }

    open spec fn new_pre() -> bool {
        obeys_key_model::<Key>()
    }

    fn new() 
        -> (out: (Self, Tracked<KVStoreSM::client<Key, usize>>))
    // ensures
    //     out.0.inv(),
    //     out.1@.valid(out.0.id(), 1),
    //     forall |k: Key| #![trigger out.1@.val().contains_key(k)]
    //     {
    //         &&& !out.1@.val().contains_key(k)
    //     };
    {
        let mut phy = HashMap::new();

        let tracked (
            Tracked(inst),
            Tracked(inner),
            Tracked(client)
        ) = KVStoreSM::Instance::initialize(Map::<Key, usize>::empty(), Map::<Key, usize>::empty());

        let state = HashKVState { 
            phy: phy,
            inst: Tracked(inst),
            inner: Tracked(inner)
        };

        let ghost pred = KVPred { 
            id: inst.id()
        };

        let locked_state = RwLock::new(state, Ghost(pred));

        (HashKVStore{locked_state}, Tracked(client))
    }

    fn get<Lin: ReadLinearizer<KVStoreGetOperation<Key, usize>>>(&self, k: Key, Tracked(lin): Tracked<Lin>) 
        -> (out: (Option::<usize>, Tracked<Lin::ApplyResult>))
    // requires
    //     self.inv(),
    //     lin@.pre(self.get_op(k))
    // ensures 
    //     lin@.post(self.get_op(k), out.0, out.1@)
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let phy_result_ref = state.phy.get(&k);
        let phy_result = if phy_result_ref.is_some() { Some(*phy_result_ref.unwrap()) } else { None };  // could use clone + extra assumption about equality
        
        let tracked ar = lin.apply(get_op(self.id(), k), state.inst, &state.inner, &phy_result);

        read_handle.release_read();
        (phy_result, Tracked(ar))
    }

    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, usize>>>(&self, k: Key, v: usize, tracked lin: &mut Lin) 
        -> (out: Tracked<Lin::ApplyResult>)
    // requires
    //     old(self).inv(),
    //     lin@.pre(old(self).put_op(k, v))
    // ensures
    //     self.inv(),
    //     self.id() == old(self).id(),
    //     lin@.post(old(self).put_op(k, v), (), out@)
    {   
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost op = put_op(self.id(), k, v);
        let ghost old_phy = state.phy@;

        state.phy.insert(k, v);

        let tracked ar = lin.apply(op, (), state.inst, state.inner.borrow_mut(), &());

        lock_handle.release_write(state);
        Tracked(ar)
    }
}

}