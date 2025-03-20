use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use std::sync::Arc;
use crate::frac::*;
use crate::logatom::*;
use crate::kvstore::*;
use crate::bank::*;
use crate::shardedbank::*;

verus! {

/// atomic invariant
struct ShardedBankInvK {
    bank_id: int,
    left_shard_id: int,
    right_shard_id: int
}

struct ShardedBankInvV {
    bank: FractionalResource<Map::<u32, u32>, 2>,
    left_shard: FractionalResource<Map::<u32, u32>, 2>,
    right_shard: FractionalResource<Map::<u32, u32>, 2>
}

struct ShardedBankInvPred {
}

impl InvariantPredicate<ShardedBankInvK, ShardedBankInvV> for ShardedBankInvPred {
    closed spec fn inv(k: ShardedBankInvK, v: ShardedBankInvV) -> bool
    {
        &&& v.bank.valid(k.bank_id, 1)
        &&& v.left_shard.valid(k.left_shard_id, 1)
        &&& v.right_shard.valid(k.right_shard_id, 1)
        &&& forall |k: u32| #![trigger v.bank.val().contains_key(k)] {
            sum_option_spec(val_or_none(v.left_shard.val(), k), val_or_none(v.right_shard.val(), k), val_or_none(v.bank.val(), k))
        }
    }
}

/// lock (per single shard)
struct ShardedBankLockState {
    shard: Tracked<FractionalResource<Map::<u32, u32>, 2>>,
    kv_client: Tracked<FractionalResource<Map::<u32, u32>, 2>>,
}

struct ShardedBankLockPred {
    shard_id: int,
    kv_id: int
}

impl RwLockPredicate<ShardedBankLockState> for ShardedBankLockPred {
    closed spec fn inv(self, v: ShardedBankLockState) -> bool {
        &&& v.shard@.valid(self.shard_id, 1)
        &&& v.kv_client@.valid(self.kv_id, 1)
        &&& v.shard@.val() == v.kv_client@.val()
    }
}

struct TwoLockShardedBank<Store: KVStore<u32, u32>>  {
    left_lock: RwLock<ShardedBankLockState, ShardedBankLockPred>,
    right_lock: RwLock<ShardedBankLockState, ShardedBankLockPred>,
    invariant: Tracked<Arc<AtomicInvariant<ShardedBankInvK, ShardedBankInvV, ShardedBankInvPred>>>,
    left_store: Store,
    right_store: Store
}

impl<Store: KVStore<u32, u32>> Bank for TwoLockShardedBank<Store> {
    closed spec fn id(&self) -> int {
        self.invariant@.constant().bank_id
    }

    closed spec fn inv_namespace(self) -> int {
        self.invariant@.namespace()
    }

    closed spec fn inv(&self) -> bool {
        &&& self.left_store.inv()
        &&& self.right_store.inv()
        &&& self.left_store.id() == self.left_lock.pred().kv_id
        &&& self.right_store.id() == self.right_lock.pred().kv_id
        &&& self.left_lock.pred().shard_id == self.invariant@.constant().left_shard_id
        &&& self.right_lock.pred().shard_id == self.invariant@.constant().right_shard_id
    }

    open spec fn new_pre() -> bool {
        Store::new_pre()
    }

    fn new() 
        -> (out: (Self, Tracked<FractionalResource<Map::<u32, u32>, 2>>))
    {
        let (left_store, left_client) = Store::new();
        let (right_store, right_client) = Store::new();
        let tracked(my_frac, client_frac) = FractionalResource::new(Map::<u32, u32>::empty()).split(1);
        let tracked(left_shard_my, left_shard_inv) = FractionalResource::new(Map::<u32, u32>::empty()).split(1);
        let tracked(right_shard_my, right_shard_inv) = FractionalResource::new(Map::<u32, u32>::empty()).split(1);

        let left_lock_state = ShardedBankLockState { shard: Tracked(left_shard_my), kv_client: left_client };
        let ghost left_lock_pred = ShardedBankLockPred { shard_id: left_shard_my.id(), kv_id: left_client@.id() };
        let left_lock = RwLock::new(left_lock_state, Ghost(left_lock_pred));
        let right_lock_state = ShardedBankLockState { shard: Tracked(right_shard_my), kv_client: right_client };
        let ghost right_lock_pred = ShardedBankLockPred { shard_id: right_shard_my.id(), kv_id: right_client@.id() };
        let right_lock = RwLock::new(right_lock_state, Ghost(right_lock_pred));

        let ghost inv_k = ShardedBankInvK{ 
            bank_id: my_frac.id(),  
            left_shard_id: left_shard_inv.id(),
            right_shard_id: right_shard_inv.id()
        };
        let tracked inv_v = ShardedBankInvV {
            bank: my_frac,
            left_shard: left_shard_inv,
            right_shard: right_shard_inv
        };
        let tracked inv = Arc::new(AtomicInvariant::<_,_,ShardedBankInvPred>::new(inv_k, inv_v, 12345));

        (TwoLockShardedBank { left_lock, right_lock, invariant: Tracked(inv), left_store, right_store }, Tracked(client_frac))
    }

    fn deposit<Lin: MutLinearizer<BankDepositOperation>>(&self, a: u32, v: u32, Tracked(lin): Tracked<Lin>) 
        -> (out: (Tracked<Lin::ApplyResult>))
    {
        let (mut state, lock_handle) = self.left_lock.acquire_write();

        let credit = create_open_invariant_credit();
        proof { 
            let tracked c = credit.get();
            open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                lin.peek(deposit_op(self.id(), a, v), &inv_val.bank);
                inv_val.left_shard.agree(state.shard.borrow()); // need to show that adding v to the left shard won't overflow
            });
        };

        let left_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.kv_client.get() });
        let (old_left, left_client) = self.left_store.get::<KVStoreExclusiveGetLinearizer>(a, left_lin);
        state.kv_client = left_client;

        let new_left_balance = sum_option(old_left, Some(v));
        let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.kv_client.get() });
        let left_client = self.left_store.put::<KVStoreExclusivePutLinearizer>(a, new_left_balance.unwrap(), put_lin);
        state.kv_client = left_client;

        let credit = create_open_invariant_credit();
        let tracked mut ar;
        let tracked mut left_shard;
        proof { 
            let tracked c = credit.get();
            open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                lin.peek(deposit_op(self.id(), a, v), &inv_val.bank); // need to show that the account *still* exists in the bank and that we *still* won't overflow!

                ar = lin.apply(deposit_op(self.id(), a, v), (), &mut inv_val.bank, &());

                left_shard = state.shard.get();
                inv_val.left_shard.combine_mut(left_shard);
                inv_val.left_shard.update_mut(inv_val.left_shard.val().insert(a, new_left_balance.unwrap()));
                left_shard = inv_val.left_shard.split_mut(1);
            });
        };
        state.shard = Tracked(left_shard);

        lock_handle.release_write(state);
        Tracked(ar)
    }

    fn withdraw<Lin: MutLinearizer<BankWithdrawOperation>>(&self, a: u32, v: u32, Tracked(lin): Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    {
        let (mut state, lock_handle) = self.left_lock.acquire_write();

        let credit = create_open_invariant_credit();
        proof { 
            let tracked c = credit.get();
            open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                lin.peek(withdraw_op(self.id(), a, v), &inv_val.bank);
                inv_val.left_shard.agree(state.shard.borrow());
            });
        };

        let left_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.kv_client.get() });
        let (old_left, left_client) = self.left_store.get::<KVStoreExclusiveGetLinearizer>(a, left_lin);
        state.kv_client = left_client;

        let left_withdraw_amt = if (v > unwrap_or_zero(old_left)) { unwrap_or_zero(old_left) } else { v };
        let right_withdraw_amt = if (v > unwrap_or_zero(old_left)) { v - left_withdraw_amt } else { 0 };
        let new_left_balance = diff_option(old_left, left_withdraw_amt);

        if (new_left_balance.is_some()) {
            let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.kv_client.get() });
            let left_client = self.left_store.put::<KVStoreExclusivePutLinearizer>(a, new_left_balance.unwrap(), put_lin); 
            state.kv_client = left_client;
        }

        let tracked mut ar;
        if (right_withdraw_amt > 0) { // need to withdraw from right shard
            let (mut right_state, right_lock_handle) = self.right_lock.acquire_write();

            let credit = create_open_invariant_credit();
            proof { 
                let tracked c = credit.get();
                open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                    lin.peek(withdraw_op(self.id(), a, v), &inv_val.bank);
                    inv_val.right_shard.agree(right_state.shard.borrow());
                    inv_val.left_shard.agree(state.shard.borrow());
                });
            };

            let right_lin = Tracked(KVStoreExclusiveGetLinearizer { client: right_state.kv_client.get() });
            let (old_right, right_client) = self.right_store.get::<KVStoreExclusiveGetLinearizer>(a, right_lin);
            right_state.kv_client = right_client;

            let new_right_balance = diff_option(old_right, right_withdraw_amt);
            let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: right_state.kv_client.get() });
            let right_client = self.right_store.put::<KVStoreExclusivePutLinearizer>(a, new_right_balance.unwrap(), put_lin); 
            right_state.kv_client = right_client;

            let tracked mut left_shard;
            let tracked mut right_shard;
            let credit = create_open_invariant_credit();
            proof { 
                let tracked c = credit.get();
                open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                    lin.peek(withdraw_op(self.id(), a, v), &inv_val.bank);

                    ar = lin.apply(withdraw_op(self.id(), a, v), (), &mut inv_val.bank, &());
    
                    if (new_left_balance.is_some()) {
                        left_shard = state.shard.get();
                        inv_val.left_shard.combine_mut(left_shard);
                        inv_val.left_shard.update_mut(inv_val.left_shard.val().insert(a, new_left_balance.unwrap()));
                        left_shard = inv_val.left_shard.split_mut(1);
                    } else {
                        left_shard = state.shard.get();
                    }

                    right_shard = right_state.shard.get();
                    inv_val.right_shard.combine_mut(right_shard);
                    inv_val.right_shard.update_mut(inv_val.right_shard.val().insert(a, new_right_balance.unwrap()));
                    right_shard = inv_val.right_shard.split_mut(1);
                });
            };
            state.shard = Tracked(left_shard);
            right_state.shard = Tracked(right_shard);

            right_lock_handle.release_write(right_state);

        } else if (new_left_balance.is_some()) { // only update left shard
            let tracked mut left_shard;
            let credit = create_open_invariant_credit();
            proof { 
                let tracked c = credit.get();
                open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                    lin.peek(withdraw_op(self.id(), a, v), &inv_val.bank);
    
                    ar = lin.apply(withdraw_op(self.id(), a, v), (), &mut inv_val.bank, &());
    
                    left_shard = state.shard.get();
                    inv_val.left_shard.combine_mut(left_shard);
                    inv_val.left_shard.update_mut(inv_val.left_shard.val().insert(a, new_left_balance.unwrap()));
                    left_shard = inv_val.left_shard.split_mut(1);
                });
            };
            state.shard = Tracked(left_shard);
        } else { // withdrawing 0
            assert(v == 0);
            let credit = create_open_invariant_credit();
            proof { 
                let tracked c = credit.get();
                open_atomic_invariant_in_proof!(c => self.invariant.borrow() => inv_val => {
                    lin.peek(withdraw_op(self.id(), a, v), &inv_val.bank);
    
                    ar = lin.apply(withdraw_op(self.id(), a, v), (), &mut inv_val.bank, &());
                });
            };
        }

        lock_handle.release_write(state);

        Tracked(ar)
    }
}
}