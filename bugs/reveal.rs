use vstd::prelude::*;

verus! {
    proof fn p() {
        assert(Seq::<int>::empty().to_multiset().len() == 0);
        reveal(Seq::to_multiset);
    }
}
