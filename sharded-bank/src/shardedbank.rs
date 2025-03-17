use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use crate::frac::*;
use crate::logatom::*;
use crate::kvstore::*;
use crate::bank::*;

verus! {

pub open spec fn val_or_none(m: Map::<u32, u32>, k: u32) -> Option::<u32>
{
    if m.contains_key(k) { Some(m[k]) } else { None::<u32> }
}

pub open spec fn unwrap_or_zero_spec(val: Option::<u32>) -> u32
{
    match val {
        None => 0,
        Some(v) => v
    }
}
    
pub fn unwrap_or_zero(val: Option<u32>) -> (out: u32)
    ensures out == unwrap_or_zero_spec(val)
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
    requires unwrap_or_zero_spec(v1) + unwrap_or_zero_spec(v2) <= u32::MAX
    ensures sum_option_spec(v1, v2, out)
{
    match (v1, v2) {
        (None, None) => None,
        (Some(v), None) => Some(v),
        (None, Some(v)) => Some(v),
        (Some(v1), Some(v2)) => Some(v1 + v2)
    }
}

pub open spec fn diff_option_spec(v1: Option::<u32>, v2: u32, diff: Option<u32>) -> bool
{
    match v1 {
        None => diff.is_none(),
        Some(v) => diff.is_some() && diff.unwrap() == v - v2
    }
}

pub fn diff_option(v1: Option::<u32>, v2: u32) -> (out: Option::<u32>)
    requires v2 <= unwrap_or_zero_spec(v1)
    ensures diff_option_spec(v1, v2, out)
{
    match v1 {
        None => None,
        Some(v) => Some(v - v2),
    }
}


struct ShardedBankInvK {
    bank_id: int,
    left_client_id: int,
    right_client_id: int,
    left_locked_id: int,
    right_locked_id: int
}

struct ShardedBankInvV {
    bank_owned: FractionalResource<Map::<u32, u32>, 2>,
    left_client: FractionalResource<Map::<u32, u32>, 2>,
    right_client: FractionalResource<Map::<u32, u32>, 2>,
    left_locked: FractionalResource<Map::<u32, u32>, 2>,
    right_locked: FractionalResource<Map::<u32, u32>, 2>
}

struct ShardedBankInvPred {
}

impl InvariantPredicate<ShardedBankInvK, ShardedBankInvV> for ShardedBankInvPred {
    closed spec fn inv(k: ShardedBankInvK, v: ShardedBankInvV) -> bool
    {
        &&& v.bank_owned.valid(k.bank_id, 1)
        &&& v.left_client.valid(k.left_client_id, 1)
        &&& v.right_client.valid(k.right_client_id, 1)
        &&& v.left_locked.valid(k.left_locked_id, 1)
        &&& v.right_locked.valid(k.right_locked_id, 1)
        &&& v.left_client.val() == v.left_locked.val()
        &&& v.right_client.val() == v.right_locked.val()
        &&& forall |k: u32| #![trigger v.bank_owned.val().contains_key(k)] {
            sum_option_spec(val_or_none(v.left_client.val(), k), val_or_none(v.right_client.val(), k), val_or_none(v.bank_owned.val(), k))
        }
    }
}

struct ShardedBankLockState {
    locked_rsrc: Tracked<FractionalResource<Map::<u32, u32>, 2>>,
}

struct ShardedBankLockPred {
    id: int,
}

impl RwLockPredicate<ShardedBankLockState> for ShardedBankLockPred {
    closed spec fn inv(self, v: ShardedBankLockState) -> bool {
        &&& v.locked_rsrc@.valid(self.id, 1)
    }
}

struct ShardedBank<Store: KVStore<u32, u32>>  {
    left_lock: RwLock<ShardedBankLockState, ShardedBankLockPred>,
    right_lock: RwLock<ShardedBankLockState, ShardedBankLockPred>,
    invariant: Tracked<AtomicInvariant<ShardedBankInvK, ShardedBankInvV, ShardedBankInvPred>>,
    left_store: Store,
    right_store: Store
}

struct KVStoreExclusiveGetLinearizer {
    pub client: FractionalResource<Map::<u32, u32>, 2>,
}

impl ReadLinearizer<KVStoreGetOperation<u32, u32>> for KVStoreExclusiveGetLinearizer {
    type ApplyResult = FractionalResource<Map::<u32, u32>, 2>;

    open spec fn pre(self, op: KVStoreGetOperation<u32, u32>) -> bool {
        self.client.valid(op.id, 1)
    }

    open spec fn post(self, op: KVStoreGetOperation<u32, u32>, r: <KVStoreGetOperation<u32, u32> as ReadOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.valid(op.id, 1)
        &&& match r {
            None => !ar.val().contains_key(op.k),
            Some(v) => ar.val().contains_key(op.k) && ar.val()[op.k] == v
        }
        &&& self.client.val() == ar.val()
    }

    proof fn apply(tracked self, op: KVStoreGetOperation<u32, u32>, tracked r: &<KVStoreGetOperation<u32, u32> as ReadOperation>::Resource, e: &<KVStoreGetOperation<u32, u32> as ReadOperation>::ExecResult) -> (tracked out: Self::ApplyResult) {
        self.client.agree(r.borrow());
        self.client
    }

    proof fn peek(tracked &self, op: KVStoreGetOperation<u32, u32>, tracked r: &<KVStoreGetOperation<u32, u32> as ReadOperation>::Resource) {}
}

struct KVStoreExclusivePutLinearizer {
    pub client: FractionalResource<Map::<u32, u32>, 2>,
}

impl MutLinearizer<KVStorePutOperation<u32, u32>> for KVStoreExclusivePutLinearizer {
    type ApplyResult = FractionalResource<Map::<u32, u32>, 2>;

    open spec fn pre(self, op: KVStorePutOperation<u32, u32>) -> bool {
        self.client.valid(op.id, 1)
    }

    open spec fn post(self, op: KVStorePutOperation<u32, u32>, r: <KVStorePutOperation<u32, u32> as MutOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.valid(op.id, 1)
        &&& ar.val() == self.client.val().insert(op.k, op.v)
    }

    proof fn apply(tracked self, op: KVStorePutOperation<u32, u32>, hint: <KVStorePutOperation<u32, u32> as MutOperation>::ApplyHint, tracked r: &mut <KVStorePutOperation<u32, u32> as MutOperation>::Resource, e: &<KVStorePutOperation<u32, u32> as MutOperation>::ExecResult) -> (tracked out: Self::ApplyResult) {
        r.combine_mut(self.client);
        r.update_mut(r.val().insert(op.k, op.v));
        let tracked out = r.split_mut(1);
        out
    }

    proof fn peek(tracked &self, op: KVStorePutOperation<u32, u32>, tracked r: &<KVStorePutOperation<u32, u32> as MutOperation>::Resource) {}
}

impl<Store: KVStore<u32, u32>> Bank for ShardedBank<Store> {
    closed spec fn id(&self) -> int {
        self.invariant@.constant().bank_id
    }

    closed spec fn inv_namespace(self) -> int {
        12345
    }

    closed spec fn inv(&self) -> bool {
        &&& self.left_store.inv()
        &&& self.right_store.inv()
        &&& self.left_store.id() == self.invariant@.constant().left_client_id
        &&& self.right_store.id() == self.invariant@.constant().right_client_id
        &&& self.left_lock.pred().id == self.invariant@.constant().left_locked_id
        &&& self.right_lock.pred().id == self.invariant@.constant().right_locked_id
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
        let tracked(left_locked_my, left_locked_inv) = FractionalResource::new(Map::<u32, u32>::empty()).split(1);
        let tracked(right_locked_my, right_locked_inv) = FractionalResource::new(Map::<u32, u32>::empty()).split(1);

        let left_lock_state = ShardedBankLockState { locked_rsrc: Tracked(left_locked_my) };
        let ghost left_lock_pred = ShardedBankLockPred { id: left_locked_my.id() };
        let left_lock = RwLock::new(left_lock_state, Ghost(left_lock_pred));
        let right_lock_state = ShardedBankLockState { locked_rsrc: Tracked(right_locked_my) };
        let ghost right_lock_pred = ShardedBankLockPred { id: right_locked_my.id() };
        let right_lock = RwLock::new(right_lock_state, Ghost(right_lock_pred));

        let ghost inv_k = ShardedBankInvK{ 
            bank_id: my_frac.id(), 
            left_client_id: left_client@.id(), 
            right_client_id: right_client@.id(), 
            left_locked_id: left_locked_inv.id(),
            right_locked_id: right_locked_inv.id()
        };
        let tracked inv_v = ShardedBankInvV {
            bank_owned: my_frac,
            left_client: left_client.get(),
            right_client: right_client.get(),
            left_locked: left_locked_inv,
            right_locked: right_locked_inv
        };
        let tracked inv = AtomicInvariant::<_,_,ShardedBankInvPred>::new(inv_k, inv_v, 12345);

        (ShardedBank { left_lock, right_lock, invariant: Tracked(inv), left_store, right_store }, Tracked(client_frac))
    }

    /*
    fn deposit<Lin: MutLinearizer<BankDepositOperation>>(&self, a: u32, v: u32, lin: Tracked<Lin>) 
        -> (out: (u32, Tracked<Lin::ApplyResult>))
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        proof { lin.borrow().peek(deposit_op(self.id(), a, v), state.bank_owned.borrow()) };

        let left_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.left_client.get() });
        let (old_left, left_client) = self.left_store.get::<KVStoreExclusiveGetLinearizer>(a, left_lin);
        state.left_client = left_client;

        let right_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.right_client.get() });
        let (old_right, right_client) = self.right_store.get::<KVStoreExclusiveGetLinearizer>(a, right_lin);
        state.right_client = right_client;

        let new_left_balance = sum_option(old_left, Some(v));
        let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.left_client.get() });
        let left_client = self.left_store.put::<KVStoreExclusivePutLinearizer>(a, new_left_balance.unwrap(), put_lin);
        state.left_client = left_client;

        let new_balance = sum_option(new_left_balance, old_right).unwrap();
        let tracked ar = lin.get().apply(deposit_op(self.id(), a, v), (), state.bank_owned.borrow_mut(), &new_balance);

        lock_handle.release_write(state);
        (new_balance, Tracked(ar))
    }

    fn withdraw<Lin: MutLinearizer<BankWithdrawOperation>>(&self, a: u32, v: u32, lin: Tracked<Lin>) 
        -> (out: (u32, Tracked<Lin::ApplyResult>))
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        proof { lin.borrow().peek(withdraw_op(self.id(), a, v), state.bank_owned.borrow()) };

        let ghost ghost_left_client = state.left_client;
        let ghost ghost_bank = state.bank_owned;

        let left_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.left_client.get() });
        let (old_left, left_client) = self.left_store.get::<KVStoreExclusiveGetLinearizer>(a, left_lin);
        state.left_client = left_client;

        let right_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.right_client.get() });
        let (old_right, right_client) = self.right_store.get::<KVStoreExclusiveGetLinearizer>(a, right_lin);
        state.right_client = right_client;

        let left_withdraw_amt = if (v > unwrap_or_zero(old_left)) { unwrap_or_zero(old_left) } else { v };
        let right_withdraw_amt = if (v > unwrap_or_zero(old_left)) { v - left_withdraw_amt } else { 0 };
        let new_left_balance = diff_option(old_left, left_withdraw_amt);
        let new_right_balance = diff_option(old_right, right_withdraw_amt);

        if (left_withdraw_amt > 0) {
            let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.left_client.get() });
            let left_client = self.left_store.put::<KVStoreExclusivePutLinearizer>(a, new_left_balance.unwrap(), put_lin); 
            state.left_client = left_client;
        }

        if (right_withdraw_amt > 0) {
            let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.right_client.get() });
            let right_client = self.right_store.put::<KVStoreExclusivePutLinearizer>(a, new_right_balance.unwrap(), put_lin); 
            state.right_client = right_client;
        }

        let new_balance = sum_option(new_left_balance, new_right_balance).unwrap();
        let tracked ar = lin.get().apply(withdraw_op(self.id(), a, v), (), state.bank_owned.borrow_mut(), &new_balance);

        lock_handle.release_write(state);
        (new_balance, Tracked(ar))
    }
    */
}
}