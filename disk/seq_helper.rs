use vstd::prelude::*;

verus! {
    pub open spec fn update_seq<V>(s: Seq<V>, off: int, v: Seq<V>) -> Seq<V> {
        Seq::new(s.len(), |i: int| if off <= i < off + v.len() { v[i - off] } else { s[i] })
    }

    pub open spec fn update_seq_map_int<V>(s: Seq<V>, m: Map<int, V>) -> Seq<V>
        recommends
            forall |i| m.contains_key(i) ==> 0 <= i < s.len()
    {
        Seq::new(s.len(), |i: int| if m.contains_key(i) { m[i] } else { s[i] })
    }

    pub open spec fn update_seq_map_usize<V>(s: Seq<V>, m: Map<usize, V>) -> Seq<V>
        recommends
            forall |i| m.contains_key(i) ==> 0 <= i < s.len()
    {
        Seq::new(s.len(), |i: int| if m.contains_key(i as usize) { m[i as usize] } else { s[i] })
    }

    pub open spec fn seq_to_map_int<V>(s: Seq<V>, off: int) -> Map<int, V> {
        Map::new(|i: int| off <= i < off + s.len(), |i: int| s[i-off])
    }

    pub open spec fn seq_to_map_usize<V>(s: Seq<V>, off: usize) -> Map<usize, V> {
        Map::new(|i: usize| off <= i < off + s.len(), |i: usize| s[i-off])
    }
}
