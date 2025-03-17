use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;

verus! {
tokenized_state_machine! {
    GhostInterface<T> {
        fields {
            #[sharding(variable)]
            pub inner: T,

            #[sharding(variable)]
            pub client: T
        }

        init! {
            initialize(val: T) {
                init inner = val;
                init client = val;
            }
        }

        property! {
            agree() {
                assert pre.inner == pre.client by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            update(new_val: T) {
                update inner = new_val;
                update client = new_val;
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            self.inner == self.client
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, val: T) { }

        #[inductive(update)]
        fn update_inductive(pre: Self, post: Self, new_val: T) { }
    }
}
}