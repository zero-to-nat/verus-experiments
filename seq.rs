use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
    // If, in a sequence's conversion to a multiset, each element occurs only once,
    // the sequence has no duplicates.
    pub proof fn lemma_multiset_has_no_duplicates<A>(s: Seq<A>)
        requires
            forall|x: A| s.to_multiset().contains(x) ==> s.to_multiset().count(x) == 1
        ensures
            s.no_duplicates()
    {
        assert forall|i, j| (0 <= i < s.len() && 0 <= j < s.len() && i != j) implies s[i] != s[j] by {
            let mut a = if (i < j) { i } else { j };
            let mut b = if (i < j) { j } else { i };

            if (s[a] == s[b]) {
                let s0 = s.subrange(0, b);
                let s1 = s.subrange(b, s.len() as int);
                assert(s == s0 + s1);

                s0.to_multiset_ensures();
                s1.to_multiset_ensures();

                lemma_multiset_commutative(s0, s1);
                assert(s.to_multiset().count(s[a]) >= 2);
            }
        }
    }
}
