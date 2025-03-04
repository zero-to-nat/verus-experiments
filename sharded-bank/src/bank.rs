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

pub struct ShardedBankDepositSemantics {}

impl CallBackSemantics for ShardedBankDepositSemantics {
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

struct ShardedBankDepositCB {
    pub rsrc: FractionalResource<Option::<u32>, 2>,
}

impl GenericSingleInvCallBack<ShardedBankDepositSemantics> for ShardedBankDepositCB {
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
    left_store: Store,
    left_down_frac_map: Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>,
    right_store: Store,
    right_down_frac_map: Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>,
    up_frac_map: Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>,
}

struct ShardedBankPred {
    ids: Map<u32, int>
}

impl<Store: KVStore<u32, u32>> RwLockPredicate<ShardedBankState<Store>> for ShardedBankPred {
    closed spec fn inv(self, v: ShardedBankState<Store>) -> bool {
        &&& forall |k: u32|
            #![trigger self.ids.contains_key(k)]
            #![trigger v.left_down_frac_map@.contains_key(k)]
            #![trigger v.right_down_frac_map@.contains_key(k)]
            #![trigger v.up_frac_map@.contains_key(k)]
            0 <= k <= u32::MAX ==> 
        {
            &&& self.ids.contains_key(k)
            &&& v.left_store.ids().contains_key(k)
            &&& v.left_down_frac_map@.contains_key(k)
            &&& v.left_down_frac_map@[k].valid(v.left_store.ids()[k], 1)
            &&& v.right_store.ids().contains_key(k)
            &&& v.right_down_frac_map@.contains_key(k)
            &&& v.right_down_frac_map@[k].valid(v.right_store.ids()[k], 1)
            &&& v.up_frac_map@.contains_key(k)
            &&& v.up_frac_map@[k].valid(self.ids[k], 1)
            &&& ShardedBank::<Store>::unwrap_or_zero(v.left_down_frac_map@[k].val()) + ShardedBank::<Store>::unwrap_or_zero(v.right_down_frac_map@[k].val()) <= u32::MAX
            &&& ShardedBank::<Store>::sum_option_spec(v.left_down_frac_map@[k].val(), v.right_down_frac_map@[k].val(), v.up_frac_map@[k].val())
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

    pub open spec fn unwrap_or_zero(val: Option::<u32>) -> u32
    {
        match val {
            None => 0,
            Some(v) => v
        }
    }

    pub open spec fn sum_option_spec(v1: Option::<u32>, v2: Option::<u32>, sum: Option<u32>) -> bool
    {
        match (v1, v2) {
            (None, None) => sum.is_none(),
            (Some(v), None) => sum.is_some() && sum.unwrap() == v,
            (None, Some(v)) => sum.is_some() && sum.unwrap() == v,
            (Some(v1), Some(v2)) => sum.is_some() && sum.unwrap() == v1 + v2
        }
    }

    pub fn sum_option(v1: Option::<u32>, v2: Option::<u32>) -> (out: Option::<u32>)
        requires Self::unwrap_or_zero(v1) + Self::unwrap_or_zero(v2) <= u32::MAX
        ensures Self::sum_option_spec(v1, v2, out)
    {
        match (v1, v2) {
            (None, None) => None,
            (Some(v), None) => Some(v),
            (None, Some(v)) => Some(v),
            (Some(v1), Some(v2)) => Some(v1 + v2)
        }
    }

    proof fn compute_new_total(old_total: Option<u32>, old_shard1: Option<u32>, new_shard1: u32, shard2: Option<u32>) -> (new_total: u32)
        requires 
            Self::sum_option_spec(old_shard1, shard2, old_total),
            Self::unwrap_or_zero(old_total) - Self::unwrap_or_zero(old_shard1) + new_shard1 <= u32::MAX
        ensures 
            Self::sum_option_spec(Some(new_shard1), shard2, Some(new_total)),
    {
        let mut new_total: int;
        if (old_total.is_none()) {
            assert(old_shard1.is_none());
            assert(shard2.is_none());
            new_total = new_shard1 as int;
        } else {
            assert(old_total.unwrap() >= Self::unwrap_or_zero(old_shard1));
            new_total = old_total.unwrap() - Self::unwrap_or_zero(old_shard1) + new_shard1;
        }
        new_total as u32
    }

    fn new() -> (out: (Self, Tracked<Map<u32, FractionalResource<Option::<u32>, 2>>>))
        ensures
            forall |k: u32| 0 <= k <= u32::MAX ==>
            {
                &&& #[trigger] out.0.ids().contains_key(k)
                &&& out.1@[k].val() == None::<u32>
            }
    {
        let (left_store, left_down_fracs) = Store::new();
        let (right_store, right_down_fracs) = Store::new();

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

        let state = ShardedBankState { 
            left_store: left_store, 
            left_down_frac_map: left_down_fracs, 
            right_store: right_store,
            right_down_frac_map: right_down_fracs,
            up_frac_map: Tracked(my_fracs) 
        };
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

        let tracked left_down_frac = state.left_down_frac_map.borrow().tracked_borrow(k);
        let left_cb: Tracked<KVStoreGetCB<u32>> = Tracked(KVStoreGetCB{rsrc: Tracked(left_down_frac)}); 
        let (left_phy_result, _) = state.left_store.get(k, left_cb);
        let tracked right_down_frac = state.right_down_frac_map.borrow().tracked_borrow(k);
        let right_cb: Tracked<KVStoreGetCB<u32>> = Tracked(KVStoreGetCB{rsrc: Tracked(right_down_frac)}); 
        let (right_phy_result, _) = state.right_store.get(k, right_cb);

        let total = Self::sum_option(left_phy_result, right_phy_result);

        let bank_cb: Tracked<ShardedBankGetCB> = Tracked(ShardedBankGetCB{rsrc: client_frac});
        let tracked up_frac = state.up_frac_map.borrow().tracked_borrow(k);
        let tracked (_, _) = bank_cb.get().cb(&up_frac, &total);

        read_handle.release_read();

        total
    }

    fn deposit(&self, k: u32, v: u32, client_frac: FractionalResource<Option::<u32>, 2>) 
        -> (out: Tracked<FractionalResource<Option::<u32>, 2>>)
        requires
            self.ids().contains_key(k),
            client_frac.valid(self.ids()[k], 1),
            Self::unwrap_or_zero(client_frac.val()) + v <= u32::MAX
        ensures 
            out@.valid(self.ids()[k], 1),
            out@.val().is_some(),
            out@.val().unwrap() == Self::unwrap_or_zero(client_frac.val()) + v
    {   
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        // first, read old value
        let tracked down_frac = state.left_down_frac_map.borrow().tracked_borrow(k);
        let get_cb: Tracked<KVStoreGetCB<u32>> = Tracked(KVStoreGetCB{rsrc: Tracked(down_frac)}); 
        let (old_phy_result, _) = state.left_store.get(k, get_cb);

        // second, add deposit and write new value
        let tracked up_frac = state.up_frac_map.borrow_mut().tracked_remove(k);
        proof {
            client_frac.agree(&up_frac);
        }
        assert(Self::unwrap_or_zero(old_phy_result) <= Self::unwrap_or_zero(client_frac.val()));
        let new_phy_result = Self::sum_option(old_phy_result, Some(v));
        let tracked down_frac = state.left_down_frac_map.borrow_mut().tracked_remove(k);
        let set_cb: Tracked<KVStoreSetCB<u32>> = Tracked(KVStoreSetCB{rsrc: down_frac}); 
        let Tracked(cbresult) = state.left_store.set(k, new_phy_result.unwrap(), set_cb);
        let tracked _ = state.left_down_frac_map.borrow_mut().tracked_insert(k, cbresult); 

        // third, update bank's ghost resources
        assert(Self::unwrap_or_zero(up_frac.val()) + v == Self::unwrap_or_zero(state.left_down_frac_map@[k].val()) + Self::unwrap_or_zero(state.right_down_frac_map@[k].val()));
        let ghost new_total = (Self::unwrap_or_zero(up_frac.val()) + v) as u32;
        let bank_cb: Tracked<ShardedBankDepositCB> = Tracked(ShardedBankDepositCB{rsrc: client_frac});
        let tracked (new_up_frac, new_client_frac) = bank_cb.get().cb(up_frac, &new_total);
        proof {
            new_client_frac.agree(&new_up_frac);
        }
        let tracked _ = state.up_frac_map.borrow_mut().tracked_insert(k, new_up_frac);

        lock_handle.release_write(state);

        Tracked(new_client_frac)
    }
}
}