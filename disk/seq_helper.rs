use vstd::prelude::*;

verus! {
    pub open spec fn update_seq<V>(s: Seq<V>, off: int, v: Seq<V>) -> Seq<V> {
        Seq::new(s.len(), |i: int| if off <= i < off + v.len() { v[i - off] } else { s[i] })
    }
}
