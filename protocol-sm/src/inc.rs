use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;

verus! {

tokenized_state_machine! {
    AtMostOnceProtocol<T> {
        fields {
            #[sharding(constant)]
            pub once_args: T,

            #[sharding(constant)]
            pub always_args: T,

            #[sharding(variable)]
            pub has_once_perm: bool,

            #[sharding(map)]
            pub perms: Map<nat, T>,
        }

        init! {
            initialize(once_args: T, always_args: T) {
                require once_args != always_args;
                init once_args = once_args;
                init always_args = always_args;
                init has_once_perm = false;
                init perms = Map::<nat, T>::empty();
            }
        }

        property! {
            before_has_once_perm(n: nat, v: T) {
                require !pre.has_once_perm;
                have perms >= [n => v];
                assert v == pre.always_args by {
                    assert(pre.inv());
                };
            }
        }

        property! {
            after_has_once_perm(n: nat, v: T) {
                require pre.has_once_perm;
                have perms >= [n => v];
                assert v == pre.once_args || v == pre.always_args by {
                    assert(pre.inv());
                };
            }
        }

        property! {
            at_most_once(n1: nat, v1: T, n2: nat, v2: T) {
                have perms >= [n1 => v1];
                have perms >= [n2 => v2];
                assert v1 == v2 ==> n1 == n2 || v1 == pre.always_args by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            get_always_perm() {
                birds_eye let n = pre.perms.len();
                add perms += [ n => pre.always_args ];
            }
        }

        transition! {
            get_once_perm() {
                require !pre.has_once_perm;
                birds_eye let n = pre.perms.len();
                add perms += [ n => pre.once_args ];
                update has_once_perm = true;
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& self.once_args != self.always_args
            &&& (forall |n: nat| #[trigger] self.perms.dom().contains(n) ==> 0 <= n < self.perms.len())
            &&& !self.has_once_perm ==> (forall |n: nat| #[trigger] self.perms.dom().contains(n) ==> self.perms[n] == self.always_args)
            &&& (forall |n, m| {
                &&& #[trigger] self.perms.dom().contains(n) 
                &&& #[trigger] self.perms.dom().contains(m) 
                &&& self.perms[n] == self.once_args 
                &&& self.perms[m] == self.once_args
            } ==> {
                n == m
            })
            &&& (forall |n: nat| #[trigger] self.perms.dom().contains(n) ==> self.perms[n] == self.once_args || self.perms[n] == self.always_args)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, once_args: T, always_args: T) { 
            assert forall |n: nat| #[trigger] post.perms.dom().contains(n) implies false by {}
        }
       
        #[inductive(get_always_perm)]
        fn get_always_perm_inductive(pre: Self, post: Self) {
            assert forall |n: nat| #[trigger] post.perms.dom().contains(n) implies 0 <= n < post.perms.len() by {
                if (pre.perms.dom().contains(n)) {
                    assert(post.perms == pre.perms.insert(pre.perms.len(), pre.always_args));
                    assume(post.perms.len() >= pre.perms.len());
                } else {
                    assert(n == pre.perms.len());
                    assume(post.perms.len() > pre.perms.len());
                }
            }
        }

        #[inductive(get_once_perm)]
        fn get_once_perm_inductive(pre: Self, post: Self) { 
            assert forall |n: nat| #[trigger] post.perms.dom().contains(n) implies 0 <= n < post.perms.len() by {
                if (pre.perms.dom().contains(n)) {
                    assert(post.perms == pre.perms.insert(pre.perms.len(), pre.once_args));
                    assume(post.perms.len() >= pre.perms.len());
                } else {
                    assert(n == pre.perms.len());
                    assume(post.perms.len() > pre.perms.len());
                }
            }
        }
    }
}

// todo: brain dump
// should fetchadd maintain a single variable of the used perms
// and then the module provides a proof fn which returns a shared ref to all the used perms
tokenized_state_machine! {
    #[verifier::reject_recursive_types(P)]
    FetchAdd<P: KeyValueToken<nat, u32>> {
        fields {
            #[sharding(constant)]
            pub client_id: InstanceId,

            // we need to use a storage protocol so that we can get back something Tracked --
            // either as a shared reference or as mutable ownership
            #[sharding(storage_map)]
            pub perms: Map<nat, Tracked<P>>,

            // but we also need to have a way for clients to keep track of what has been deposited so that they can guard it...
            // so this is like a history of the deposited perms
            #[sharding(persistent_map)]
            pub used_perms: Map<nat, Tracked<P>>,

            #[sharding(persistent_map)]
            pub hist: Map<nat, u32>,

            // here we have to explicitly keep track of the length of the history:
            // Verus forbids us from using birds_eye to deposit something in the storage map
            #[sharding(variable)]
            pub len: nat,

            #[sharding(variable)]
            pub inner: u32,
        }

        init! {
            initialize(id: InstanceId, v: u32, p: Tracked<P>) {
                require p@.instance_id() == id;
                require p@.value() == v;
                init client_id = id;
                init hist = Map::<nat, u32>::empty().insert(0, v);
                init perms = Map::<nat, Tracked<P>>::empty().insert(0, p);
                init used_perms = Map::<nat, Tracked<P>>::empty().insert(0, p);
                init len = 1;
                init inner = v;
            }
        }

        property! {
            // we can guard a used perm, even if we don't know the value
            borrow_perm(n: nat) {
                require n < pre.len;
                have used_perms >= [n => let p];
                guard perms >= [n => p];
            }
        }

        transition! {
            fetch_add(perm: Tracked<P>, v: u32) {
                require perm@.instance_id() == pre.client_id;
                require perm@.value() == v;
                require (pre.inner + v) as u32 <= u32::MAX;
                let n = pre.len;

                update inner = (pre.inner + v) as u32;
                update len = pre.len + 1;
                add hist (union)= [n => (pre.inner + v) as u32];
                add used_perms (union)= [n => perm];
                deposit perms += [n => perm];
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& self.len == self.hist.len()
            &&& self.hist.dom() == self.perms.dom() 
            && self.perms.dom() == self.used_perms.dom()
            &&& (forall |n: nat| #[trigger] self.hist.dom().contains(n) ==> 0 <= n < self.hist.len())
            &&& (forall |n: nat| #[trigger] self.hist.dom().contains(n) && n > 0 ==> {
                self.hist[n] == (self.hist[(n - 1) as nat] + self.perms[n]@.value()) as u32
            })
            &&& (forall |n: nat| #[trigger] self.hist.dom().contains(n) && n > 0 ==> {
                exists |p: Tracked<P>| {
                    &&& self.perms[n] == p
                    &&& self.hist[n] == (self.hist[(n - 1) as nat] + p@.value()) as u32
                }
            })
            &&& (forall |n:nat| #[trigger] self.hist.dom().contains(n) ==> {
                self.perms[n]@.instance_id() == self.client_id
            })
            &&& (forall |n:nat| #[trigger] self.perms.dom().contains(n) ==> {
                self.perms[n] == self.used_perms[n]
            })
            &&& self.inner == self.hist[(self.hist.len() - 1) as nat]
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, id: InstanceId, v: u32, p: Tracked<P>) { 
            assert forall |n: nat| #[trigger] post.hist.dom().contains(n) implies n == 0 by {}
        }
       
        #[inductive(fetch_add)]
        fn fetch_add_inductive(pre: Self, post: Self, perm: Tracked<P>, v: u32) {
            assert(post.hist.dom() == pre.hist.insert(pre.hist.len(), (pre.inner + v) as u32).dom());
            assert(pre.hist.insert(pre.hist.len(), (pre.inner + v) as u32).dom() == pre.hist.dom().insert(pre.hist.len()));
            assume(post.hist.len() == pre.hist.len() + 1);
            assert forall |n: nat| #[trigger] post.hist.dom().contains(n) implies 0 <= n < post.hist.len() by {
                if (pre.hist.dom().contains(n)) {
                    assert(post.hist == pre.hist.insert(pre.hist.len(), (pre.inner + v) as u32));
                } else {
                    assert(n == pre.hist.len());
                }
            }

            assert forall |n: nat| #[trigger] post.hist.dom().contains(n) && n > 0 implies
                post.hist[n] == (post.hist[(n - 1) as nat] + post.perms[n]@.value()) as u32
            by {
                if (pre.hist.dom().contains(n)) {
                    assert(post.hist == pre.hist.insert(pre.hist.len(), (pre.inner + v) as u32));
                    assert(post.perms == pre.perms.insert(pre.hist.len(), perm));
                    assert(post.hist[n] == (post.hist[(n - 1) as nat] + post.perms[n]@.value()) as u32);
                } else {
                    assert(n == pre.hist.len());
                    assert(post.hist == pre.hist.insert(n, (pre.inner + v) as u32));
                    assert(post.perms == pre.perms.insert(n, perm));
                    assert(post.hist[n] == (post.hist[(n - 1) as nat] + perm@.value()) as u32);
                }
            }
        }
    }
}

fn main() {
    let tracked(
        inc_protocol_inst,
        has_inc_perm,
        _
    ) = AtMostOnceProtocol::Instance::initialize(1, 0);

    let tracked (_, init_perm) = inc_protocol_inst.borrow().get_always_perm();
    let tracked perm_map = Map::<nat, Tracked<AtMostOnceProtocol::perms<u32>>>::tracked_empty();
    let tracked _ = perm_map.tracked_insert(0, init_perm);
    let tracked(
        fa_inst,
        fa_used_perms,
        fa_hist,
        fa_len,
        fa_inner
    ) = FetchAdd::Instance::initialize(inc_protocol_inst@.id(), 0, init_perm, perm_map);

    // show how to use the guard operator to get a shared reference to the used perm
    let tracked init_perm_hist = fa_used_perms.borrow_mut().remove(0);
    let tracked init_perm_ref = fa_inst.borrow().borrow_perm(0, &init_perm_hist, fa_len.borrow());
    let tracked _ = inc_protocol_inst.borrow().before_has_once_perm(init_perm_ref@.key(), init_perm_ref@.value(), has_inc_perm.borrow(), init_perm_ref.borrow());

    // fetch_add(0)
    let tracked (_, zero_perm) = inc_protocol_inst.borrow().get_always_perm();
    let tracked (zero_hist, zero_perm_hist) = fa_inst.borrow().fetch_add(zero_perm, 0, zero_perm, fa_len.borrow_mut(), fa_inner.borrow_mut());

    // fetch_add(1)
    let tracked (_, one_perm) = inc_protocol_inst.borrow().get_once_perm(has_inc_perm.borrow_mut());
    let tracked (one_hist, one_perm_hist) = fa_inst.borrow().fetch_add(one_perm, 1, one_perm, fa_len.borrow_mut(), fa_inner.borrow_mut());
}

}