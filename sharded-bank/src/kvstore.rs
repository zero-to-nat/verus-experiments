use builtin::*;
use vstd::prelude::*;
use crate::frac::*;
use crate::callback::*;

verus! {

pub struct KVStoreGetSemantics<Value> {
    dummy: Value, // needed so that compiler will let us add type parameter
}

impl<Value> CallBackSemantics for KVStoreGetSemantics<Value> {
    type Param = FractionalResource<Option::<Value>, 2>;
    type GhostResult = ();
    type ExecResult = Option::<Value>;

    open spec fn requires(id: int, p: Self::Param, e: Self::ExecResult) -> bool
    {
        &&& p.valid(id, 1)
        &&& p.val() == e
    }

    open spec fn ensures(id: int, p: Self::Param, e: Self::GhostResult) -> bool
    {
        true
    }
}

pub struct KVStoreGetCB<'a, Value> {
    pub rsrc: Tracked<&'a FractionalResource<Option::<Value>, 2>>
}

impl<'a, Value> GenericSingleInvReadCallBack<KVStoreGetSemantics<Value>> for KVStoreGetCB<'a, Value> {
    type CBResult = ();
    
    open spec fn inv(&self) -> bool
    {
        self.rsrc@.inv()
    }

    open spec fn id(&self) -> int
    {
        self.rsrc@.id()
    }

    open spec fn inv_namespace(&self) -> int
    {
        arbitrary() // not used in sequential case
    }

    open spec fn post(&self, return_val: &Option::<Value>, result: &Self::CBResult) -> bool
    {
        return_val == self.rsrc@.val()
    }

    proof fn cb(tracked self, tracked rsrc: &FractionalResource<Option::<Value>, 2>, return_val: &Option::<Value>) 
        -> (tracked out: (<KVStoreGetSemantics<Value> as CallBackSemantics>::GhostResult, Self::CBResult))
    {
        rsrc.agree(self.rsrc.borrow());
        ((), ())
    }
}

pub struct KVStoreSetSemantics<Value> {
    dummy: Value,
}

impl<Value> CallBackSemantics for KVStoreSetSemantics<Value> {
    type Param = FractionalResource<Option::<Value>, 2>;
    type GhostResult = FractionalResource<Option::<Value>, 2>;
    type ExecResult = Value;

    open spec fn requires(id: int, p: Self::Param, e: Self::ExecResult) -> bool
    {
        p.valid(id, 1)
    }

    open spec fn ensures(id: int, p: Self::Param, e: Self::GhostResult) -> bool
    {
        &&& e.valid(id, 1)
    }
}

pub struct KVStoreSetCB<Value> {
    pub rsrc: FractionalResource<Option::<Value>, 2>,
}

impl<Value> GenericSingleInvCallBack<KVStoreSetSemantics<Value>> for KVStoreSetCB<Value> {
    type CBResult = FractionalResource<Option::<Value>, 2>;
    
    open spec fn inv(&self) -> bool
    {
        self.rsrc.valid(self.id(), 1)
    }

    open spec fn id(&self) -> int
    {
        self.rsrc.id()
    }

    open spec fn inv_namespace(&self) -> int
    {
        arbitrary() // not used in sequential case
    }

    open spec fn post(&self, set_val: &Value, result: &Self::CBResult) -> bool
    {
        &&& result.val() == Some(*set_val)
        &&& result.valid(self.id(), 1)
    }

    proof fn cb(tracked self, tracked rsrc: FractionalResource<Option::<Value>, 2>, set_val: &Value) 
    -> (tracked out: (FractionalResource<Option::<Value>, 2>, Self::CBResult))
    {
        let tracked mut new_rsrc = rsrc.combine(self.rsrc);
        new_rsrc.update_mut(Some(*set_val));
        let tracked my_part = new_rsrc.split_mut(1);
        (my_part, new_rsrc)
    }
}

pub trait KVStore<Key, Value> : Sized {
    spec fn ids(&self) -> Map<Key, int>;

    /// On initialization, this store creates one fractional resource for every possible key in the map.
    /// Each key begins with an "uninitialized" value of None to represent that it is not present in the store.
    fn new() 
        -> (out: (Self, Tracked<Map::<Key, FractionalResource<Option::<Value>, 2>>>))
    ensures forall |k: Key| 
        #![trigger out.0.ids().contains_key(k)] 
        #![trigger out.1@.contains_key(k)]
    {
        &&& out.0.ids().contains_key(k)
        &&& out.1@.contains_key(k)
        &&& out.1@[k].valid(out.0.ids()[k], 1)
        &&& out.1@[k].val() == None::<Value>
    };

    /// Returns Some if this key is in the store, returns None otherwise.
    fn get<CB: GenericSingleInvReadCallBack<KVStoreGetSemantics<Value>>>(&self, k: Key, cb: Tracked<CB>) 
        -> (out: (Option::<Value>, Tracked<CB::CBResult>))
    requires    
        self.ids().contains_key(k), 
        cb@.inv(),
        cb@.id() == self.ids()[k],
    ensures 
        cb@.post(&out.0, &out.1@)
    ;

    /// Inserts the given key-value pair into the store, overwriting the old value.
    fn set<CB: GenericSingleInvCallBack<KVStoreSetSemantics<Value>>>(&self, k: Key, v: Value, cb: Tracked<CB>) 
        -> (out: Tracked<CB::CBResult>)
    requires
        self.ids().contains_key(k), 
        cb@.inv(),
        cb@.id() == self.ids()[k],
    ensures 
        cb@.post(&v, &out@)
    ;
}

}