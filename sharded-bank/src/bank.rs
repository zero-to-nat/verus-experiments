use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;

use crate::frac::*;
use crate::callback::*;
use crate::kvstore::*;

verus! {

pub struct ShardedBankGetSemantics { }

impl CallBackSemantics for ShardedBankGetSemantics {
    type Param = FractionalResource<Option::<u32>, 2>;
    type GhostResult = ();
    type ExecResult = Option::<u32>;

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

pub struct ShardedBankGetCB<'a> {
    pub rsrc: Tracked<&'a FractionalResource<Option::<u32>, 2>>
}

impl<'a> GenericSingleInvReadCallBack<ShardedBankGetSemantics> for ShardedBankGetCB<'a> {
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

    open spec fn post(&self, return_val: &Option::<u32>, result: &Self::CBResult) -> bool
    {
        return_val == self.rsrc@.val()
    }

    proof fn cb(tracked self, tracked rsrc: &FractionalResource<Option::<u32>, 2>, return_val: &Option::<u32>) 
        -> (tracked out: (<ShardedBankGetSemantics as CallBackSemantics>::GhostResult, Self::CBResult))
    {
        rsrc.agree(self.rsrc.borrow());
        ((), ())
    }
}

pub struct ShardedBankSetSemantics {}

impl CallBackSemantics for ShardedBankSetSemantics {
    type Param = FractionalResource<Option::<u32>, 2>;
    type GhostResult = FractionalResource<Option::<u32>, 2>;
    type ExecResult = u32;

    open spec fn requires(id: int, p: Self::Param, e: Self::ExecResult) -> bool
    {
        p.valid(id, 1)
    }

    open spec fn ensures(id: int, p: Self::Param, e: Self::GhostResult) -> bool
    {
        &&& e.valid(id, 1)
    }
}

struct ShardedBankSetCB {
    pub rsrc: FractionalResource<Option::<u32>, 2>,
}

impl GenericSingleInvCallBack<ShardedBankSetSemantics> for ShardedBankSetCB {
    type CBResult = FractionalResource<Option::<u32>, 2>;
    
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

    open spec fn post(&self, set_val: &u32, result: &Self::CBResult) -> bool
    {
        &&& result.val() == Some(*set_val)
        &&& result.valid(self.id(), 1)
    }

    proof fn cb(tracked self, tracked rsrc: FractionalResource<Option::<u32>, 2>, set_val: &u32) 
    -> (tracked out: (FractionalResource<Option::<u32>, 2>, Self::CBResult))
    {
        let tracked mut new_rsrc = rsrc.combine(self.rsrc);
        new_rsrc.update_mut(Some(*set_val));
        let tracked my_part = new_rsrc.split_mut(1);
        (my_part, new_rsrc)
    }
}

struct ShardedBankState<Store: KVStore<u32, u32>> {
    phy: Store,
    down_frac_map: Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>,
    up_frac_map: Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>,
}

struct ShardedBankPred {
    ids: Map<u32, int>
}

impl<Store: KVStore<u32, u32>> RwLockPredicate<ShardedBankState<Store>> for ShardedBankPred {
    closed spec fn inv(self, v: ShardedBankState<Store>) -> bool {
        &&& forall |k: u32|
            #![trigger self.ids.contains_key(k)]
            #![trigger v.down_frac_map@.contains_key(k)]
            #![trigger v.up_frac_map@.contains_key(k)]
            0 <= k <= u32::MAX ==> 
        {
            &&& #[trigger] self.ids.contains_key(k)
            &&& v.phy.ids().contains_key(k)
            &&& v.down_frac_map@.contains_key(k)
            &&& v.down_frac_map@[k].valid(v.phy.ids()[k], 1)
            &&& v.up_frac_map@.contains_key(k)
            &&& v.up_frac_map@[k].valid(self.ids[k], 1)
            &&& v.down_frac_map@[k].val() == v.up_frac_map@[k].val()
        }
    }
}

struct ShardedBank<Store: KVStore<u32, u32>> {
    locked_state: RwLock<ShardedBankState<Store>, ShardedBankPred>,
}

impl<Store: KVStore<u32, u32>> ShardedBank<Store> {
    spec fn ids(&self) -> Map<u32, int>
    {
        self.locked_state.pred().ids
    }

    proof fn new_frac() -> (tracked out: FractionalResource<Option::<u32>, 2>) {
        let tracked frac = FractionalResource::new(None::<u32>);
        frac
    }

    fn new() -> (out: (Self, Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>))
        ensures
            forall |k: u32| 0 <= k <= u32::MAX ==>
            {
                &&& #[trigger] out.0.ids().contains_key(k)
                &&& out.1@[k].val() == None::<u32>
            }
    {
        let (phy, down_fracs) = Store::new();

        let tracked my_fracs = Map::<u32, FractionalResource<Option::<u32>, 2>>::tracked_empty();
        let tracked client_fracs = Map::<u32, FractionalResource<Option::<u32>, 2>>::tracked_empty();
        let ghost ids = Map::<u32, int>::empty();
        let mut k: u32 = 0;
        while k < u32::MAX 
            invariant 
                0 <= k <= u32::MAX,
                forall |i|
                    #![trigger my_fracs.contains_key(i)]
                    #![trigger client_fracs.contains_key(i)]
                    #![trigger ids.contains_key(i)]
                    0 <= i < k ==> 
                {
                    &&& my_fracs.contains_key(i)
                    &&& my_fracs[i].val() == None::<u32>
                    &&& client_fracs.contains_key(i)
                    &&& client_fracs[i].val() == None::<u32>
                    &&& ids.contains_key(i)
                    &&& my_fracs[i].valid(ids[i], 1)
                }
        {
            proof {
                let tracked (my_frac, client_frac) = FractionalResource::new(None::<u32>).split(1);
                my_fracs.tracked_insert(k, my_frac);
                client_fracs.tracked_insert(k, client_frac);
                ids = ids.insert(k, my_frac.id());
            }
            k = (k + 1) as u32;

        }
        proof {
            let tracked (my_frac, client_frac) = FractionalResource::new(None::<u32>).split(1);
            my_fracs.tracked_insert(u32::MAX, my_frac);
            client_fracs.tracked_insert(u32::MAX, client_frac);
            ids = ids.insert(u32::MAX, my_frac.id());
        }

        let state = ShardedBankState { phy: phy, down_frac_map: down_fracs, up_frac_map: Tracked(my_fracs) };
        let ghost pred = ShardedBankPred { ids: ids };
        let locked_state = RwLock::new(state, Ghost(pred));

        (ShardedBank { locked_state }, Tracked(client_fracs))
    }

    fn get(&self, k: u32, client_frac: Tracked<&FractionalResource<Option::<u32>, 2>>) 
        -> (out: Option::<u32>)
        requires  
            self.ids().contains_key(k),
            client_frac@.valid(self.ids()[k], 1) 
        ensures 
            client_frac@.val() == out
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let tracked down_frac = state.down_frac_map.borrow().tracked_borrow(k);
        let kv_cb: Tracked<KVStoreGetCB<u32>> = Tracked(KVStoreGetCB{rsrc: Tracked(down_frac)}); 
        let (phy_result, _) = state.phy.get(k, kv_cb);

        let bank_cb: Tracked<ShardedBankGetCB> = Tracked(ShardedBankGetCB{rsrc: client_frac});
        let tracked up_frac = state.up_frac_map.borrow().tracked_borrow(k);
        let tracked (_, _) = bank_cb.get().cb(&up_frac, &phy_result);

        read_handle.release_read();

        phy_result
    }

    fn set(&self, k: u32, v: u32, client_frac: FractionalResource<Option::<u32>, 2>) 
        -> (out: Tracked<FractionalResource<Option::<u32>, 2>>)
        requires
            self.ids().contains_key(k),
            client_frac.valid(self.ids()[k], 1) 
        ensures 
            out@.valid(self.ids()[k], 1)
    {   
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        let tracked down_frac = state.down_frac_map.borrow_mut().tracked_remove(k);
        let cb: Tracked<KVStoreSetCB<u32>> = Tracked(KVStoreSetCB{rsrc: down_frac}); 
        let Tracked(cbresult) = state.phy.set(k, v, cb);
        let tracked _ = state.down_frac_map.borrow_mut().tracked_insert(k, cbresult); 

        let bank_cb: Tracked<ShardedBankSetCB> = Tracked(ShardedBankSetCB{rsrc: client_frac});
        let tracked up_frac = state.up_frac_map.borrow_mut().tracked_remove(k);
        let tracked (new_up_frac, new_client_frac) = bank_cb.get().cb(up_frac, &v);
        proof {
            new_client_frac.agree(&new_up_frac);
        }
        let tracked _ = state.up_frac_map.borrow_mut().tracked_insert(k, new_up_frac);

        lock_handle.release_write(state);

        Tracked(new_client_frac)
    }
}
}