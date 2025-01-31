use vstd::prelude::*;

verus! {
    pub open spec fn update_seq<V>(s: Seq<V>, off: int, v: Seq<V>) -> Seq<V> {
        Seq::new(s.len(), |i: int| if off <= i < off + v.len() { v[i - off] } else { s[i] })
    }

    pub open spec fn seq_to_map<V>(s: Seq<V>, off: int) -> Map<int, V> {
        Map::new(|i| off <= i < off + s.len(), |i: int| s[i-off])
    }
}
