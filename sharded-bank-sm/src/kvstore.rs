use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;
use std::marker::PhantomData;
use crate::logatom::*;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(Key)]
    KVStoreSM<Key, Value> {
        fields {
            #[sharding(variable)]
            pub inner: Map<Key, Value>,

            #[sharding(option)]
            pub client: Option<Map<Key, Value>>
        }

        init! {
            initialize() 
            {
                init inner = Map::<Key, Value>::empty();
                init client = Some(Map::<Key, Value>::empty());
            }
        }

        property! {
            get(k: Key, v: Option<Value>) {
                have client >= Some(let cl);

                require pre.inner.contains_key(k) ==> v == Some(pre.inner[k]);
                require !pre.inner.contains_key(k) ==> v == None::<Value>;

                assert pre.inner == cl by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            put(k: Key, v: Value) {
                remove client -= Some(let old_client);

                assert (pre.inner == old_client) by {
                    assert(pre.inv());
                };

                update inner = pre.inner.insert(k, v);
                add client += Some(pre.inner.insert(k, v));
            }
        }

        property! {
            agree() {
                have client >= Some(let cl);

                assert pre.inner == cl by {
                    assert(pre.inv());
                };
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            &&& self.client.is_some()
            &&& self.inner == self.client.unwrap()
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
              
        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: Key, v: Value) { }
    }
}

/// get operation
/// is this "the same" as KVStoreSM::get ?
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
    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, Value>>>(&self, k: Key, v: Value, lin: Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    requires
        self.inv(),
        lin@.pre(put_op(self.id(), k, v))
    ensures
        lin@.post(put_op(self.id(), k, v), (), out@)
    ;
}
}