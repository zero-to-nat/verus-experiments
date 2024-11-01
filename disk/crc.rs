use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::relations::*;
use vstd::multiset::*;

verus! {
    #[verifier::inline]
    pub open spec fn popcnt_byte(a: u8) -> nat {
        let p0 = 1u8 & (a >> 0u8);
        let p1 = 1u8 & (a >> 1u8);
        let p2 = 1u8 & (a >> 2u8);
        let p3 = 1u8 & (a >> 3u8);
        let p4 = 1u8 & (a >> 4u8);
        let p5 = 1u8 & (a >> 5u8);
        let p6 = 1u8 & (a >> 6u8);
        let p7 = 1u8 & (a >> 7u8);
        let sum = add(p0, add(p1, add(p2, add(p3, add(p4, add(p5, add(p6, p7)))))));
        sum as nat
    }

    pub open spec fn sum(l: Seq<nat>) -> nat {
        l.fold_right(|i, s: nat| { s+i as nat }, 0)
    }

    pub open spec fn seq_popcnt(l: Seq<u8>) -> Seq<nat> {
        l.map_values(|v: u8| popcnt_byte(v))
    }

    pub open spec fn popcnt(l: Seq<u8>) -> nat {
        sum(seq_popcnt(l))
    }

    pub open spec fn xor(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
        a.zip_with(b).map_values(|v: (u8, u8)| v.0 ^ v.1)
    }

    pub open spec fn hamming(a: Seq<u8>, b: Seq<u8>) -> nat {
        popcnt(xor(a, b))
    }

    pub closed spec fn spec_crc64(bytes: Seq<u8>) -> Seq<u8>;

    pub open spec fn spec_crc64_hamming_bound(len: nat) -> nat {
        // From https://users.ece.cmu.edu/~koopman/crc/crc64.html as one example.
        // For the CRC64-ECMA variant.
        if len <= (32768+7)/8 {
            8
        } else if len <= (32768+7)/8 {
            7
        } else if len <= (126701+7)/8 {
            6
        } else if len <= (126701+7)/8 {
            5
        } else if len <= (8589606850+7)/8 {
            4
        } else if len <= (8589606850+7)/8 {
            3
        } else {
            2
        }
    }

    // This exec function is marked verifier::external_body to assume that the
    // implementation of CRC64 correctly matches spec_crc64().
    #[verifier::external_body]
    pub fn crc64(bytes: &[u8]) -> (out: Vec<u8>)
        ensures
            out@ == spec_crc64(bytes@)
    {
        Vec::new()
    }

    // This proof function is marked verifier::external_body to assume that all
    // CRC-64 values are 8 bytes long.
    #[verifier::external_body]
    pub proof fn crc64_spec_len(bytes: Seq<u8>)
        ensures
            spec_crc64(bytes).len() == 8,
    {}

    // This proof function is marked verifier::external_body to assume that the
    // CRC64 function, as captured by spec_crc64(), correctly achieves the hamming
    // bounds described in spec_crc64_hamming_bound.
    #[verifier::external_body]
    pub proof fn crc64_hamming_bound_valid(bytes1: Seq<u8>, bytes2: Seq<u8>, crc1: Seq<u8>, crc2: Seq<u8>)
        requires
            crc1 == spec_crc64(bytes1),
            crc2 == spec_crc64(bytes2),
            (bytes1 + crc1).len() == (bytes2 + crc2).len(),
        ensures
            bytes1 == bytes2 ||
            hamming(bytes1 + crc1, bytes2 + crc2) >= spec_crc64_hamming_bound((bytes1 + crc1).len())
    {}

    pub struct Disk {
        data: Ghost<Seq<u8>>,
        corruption: Ghost<Seq<u8>>,
        corruption_bits: Ghost<nat>,
    }

    impl Disk {
        pub closed spec fn view(&self) -> Seq<u8> { self.data@ }
        pub closed spec fn corrupt(&self) -> Seq<u8> { self.corruption@ }
        pub closed spec fn corrupt_bits(&self) -> nat { self.corruption_bits@ }

        pub closed spec fn inv(&self) -> bool {
            self.data@.len() == self.corruption@.len() && popcnt(self.corruption@) <= self.corruption_bits@
        }

        pub fn alloc(len: u64, Ghost(max_corrupt): Ghost<nat>) -> (res: Disk)
            ensures
                res.inv(),
                res@.len() == len,
        {
            let ghost disk = Seq::new(len as nat, |i: int| 0);

            // prove that there exists a Seq<u8> with a suitably low popcnt value
            assert(exists |s: Seq<u8>| #[trigger] s.len() == len && popcnt(s) <= max_corrupt) by {
                popcnt_zeroes(len as nat);
            };

            let ghost corrupt = choose |s: Seq<u8>| #[trigger] s.len() == len && popcnt(s) <= max_corrupt;
            Disk{
                data: Ghost(disk),
                corruption: Ghost(corrupt),
                corruption_bits: Ghost(max_corrupt),
            }
        }

        #[verifier::external_body]
        pub fn write(&mut self, addr: u64, val: u8)
            requires
                old(self).inv(),
                addr < old(self)@.len(),
            ensures
                self.inv(),
                self@ == old(self)@.update(addr as int, val),
                self.corrupt() == old(self).corrupt(),
                self.corrupt_bits() == old(self).corrupt_bits(),
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub fn read(&self, addr: u64) -> (res: (u8, Ghost<Seq<u8>>))
            requires
                self.inv(),
                addr < self@.len(),
            ensures
                res.1@.len() == self@.len(),
                res.0 == self@[addr as int] ^ (res.1@[addr as int] & self.corrupt()[addr as int]),
        {
            unimplemented!()
        }
    }

    pub open spec fn seq_indexes<T>(s: Seq<T>, indexes: Seq<int>) -> Seq<T> {
        indexes.map_values(|a: int| s[a])
    }

    pub proof fn seq_indexes_first<T>(s: Seq<T>, indexes: Seq<int>)
        requires
            indexes.len() > 0,
            valid_indexes(s, indexes),
        ensures
            seq_indexes(s, indexes) =~= seq![s[indexes.first()]] + seq_indexes(s, indexes.drop_first()),
            valid_index(s, indexes.first()),
            valid_indexes(s, indexes.drop_first()),
    {
    }

    pub proof fn seq_indexes_last<T>(s: Seq<T>, indexes: Seq<int>)
        requires
            indexes.len() > 0,
            valid_indexes(s, indexes),
        ensures
            seq_indexes(s, indexes) =~= seq_indexes(s, indexes.drop_last()) + seq![s[indexes.last()]],
            valid_index(s, indexes.last()),
            valid_indexes(s, indexes.drop_last()),
    {
    }

    pub proof fn seq_indexes_app<T>(s: Seq<T>, idx1: Seq<int>, idx2: Seq<int>)
        requires
            valid_indexes(s, idx1),
            valid_indexes(s, idx2),
        ensures
            seq_indexes(s, idx1 + idx2) =~= seq_indexes(s, idx1) + seq_indexes(s, idx2)
    {
    }

    pub proof fn seq_indexes_permute<T>(s: Seq<T>, idx1: Seq<int>, idx2: Seq<int>)
        requires
            valid_indexes(s, idx1),
            idx1.to_multiset() == idx2.to_multiset(),
        ensures
            seq_indexes(s, idx1).to_multiset() =~= seq_indexes(s, idx2).to_multiset()
        decreases
            idx1.len()
    {
        broadcast use vstd::multiset::group_multiset_axioms;

        valid_indexes_permute(s, idx1, idx2);
        idx1.to_multiset_ensures();
        idx2.to_multiset_ensures();
        seq_indexes(s, idx1).to_multiset_ensures();
        seq_indexes(s, idx2).to_multiset_ensures();
        if idx1.len() == 0 {
        } else {
            let i = idx1.first();
            let idx1rec = idx1.remove(0);
            assert(idx1.remove(0) == idx1.drop_first());
            assert(idx1rec.to_multiset() == idx1.to_multiset().remove(i));

            assert(idx1.to_multiset().contains(i));
            assert(idx2.contains(i));
            let idx2pos = idx2.index_of(i);
            let idx2rec = idx2.remove(idx2pos);
            idx2rec.to_multiset_ensures();
            assert(idx2rec.to_multiset() == idx2.to_multiset().remove(i));

            seq_indexes_permute(s, idx1rec, idx2rec);
            seq_indexes_first(s, idx1);
            lemma_multiset_commutative(seq![s[i]], seq_indexes(s, idx1rec));
            lemma_seq_union_to_multiset_commutative(seq![s[i]], seq_indexes(s, idx1rec));
            lemma_multiset_commutative(seq_indexes(s, idx1rec), seq![s[i]]);

            // XXX WTF
            seq![s[i]].to_multiset_ensures();
            Multiset::lemma_is_singleton(seq![s[i]].to_multiset());
            assert(seq![s[i]].len() == 1);
            assert(seq![s[i]].to_multiset().len() == 1);
            assert(seq![s[i]].to_multiset().is_singleton());
            assert(seq![s[i]].first() == s[i]);
            assert(seq![s[i]].contains(s[i]));
            assert(seq![s[i]].to_multiset().contains(s[i]));
            seq![s[i]].to_multiset().lemma_is_singleton_contains_elem_equal_singleton(s[i]);
            assert(seq![s[i]].to_multiset() =~= Multiset::singleton(s[i]));

            assert(seq_indexes(s, idx1) == seq![s[i]] + seq_indexes(s, idx1rec));
            assert(seq_indexes(s, idx1).to_multiset() == (seq![s[i]] + seq_indexes(s, idx1rec)).to_multiset());
            assert(seq_indexes(s, idx1).to_multiset() == (seq_indexes(s, idx1rec) + seq![s[i]]).to_multiset());
            assert(seq_indexes(s, idx1).to_multiset() == seq_indexes(s, idx1rec).to_multiset().add(seq![s[i]].to_multiset()));
            assert(seq_indexes(s, idx1).to_multiset() == seq_indexes(s, idx1rec).to_multiset().add(Multiset::singleton(s[i])));
            assert(seq_indexes(s, idx1).to_multiset() =~= seq_indexes(s, idx1rec).to_multiset().insert(s[i]));

            assert(seq_indexes(s, idx2rec) == seq_indexes(s, idx2).remove(idx2pos));
            assert(seq_indexes(s, idx2).to_multiset() =~= seq_indexes(s, idx2rec).to_multiset().insert(s[i]));
        }
    }

    pub proof fn seq_indexes_subrange<T>(s: Seq<T>, idx: Seq<int>, k: int)
        requires
            0 <= k <= s.len(),
            forall |i: int| 0 <= i < idx.len() ==> 0 <= #[trigger] idx[i] < k,
        ensures
            seq_indexes(s, idx) =~= seq_indexes(s.subrange(0, k), idx)
    {
    }

    pub open spec fn valid_index<T>(s: Seq<T>, i: int) -> bool {
        0 <= i < s.len()
    }

    pub open spec fn valid_indexes<T>(s: Seq<T>, indexes: Seq<int>) -> bool {
        forall |i: int| 0 <= i < indexes.len() ==> #[trigger] valid_index(s, indexes[i])
    }

    pub proof fn valid_indexes_permute<T>(s: Seq<T>, idx1: Seq<int>, idx2: Seq<int>)
        requires
            valid_indexes(s, idx1),
            idx1.to_multiset() == idx2.to_multiset(),
        ensures
            valid_indexes(s, idx2)
    {
        assert forall |i: int| 0 <= i < idx2.len() implies #[trigger] valid_index(s, idx2[i]) by {
            let idx = idx2[i];
            idx1.to_multiset_ensures();
            idx2.to_multiset_ensures();
            assert(idx2.to_multiset().count(idx) > 0);
        }
    }

    pub proof fn xor_seq_indexes(disk1: Seq<u8>, disk2: Seq<u8>, addrs: Seq<int>)
        requires
            disk1.len() == disk2.len(),
            valid_indexes(disk1, addrs),
        ensures
            xor(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs)) =~= seq_indexes(xor(disk1, disk2), addrs)
        decreases
            addrs.len()
    {
        if addrs.len() == 0 {
        } else {
            xor_seq_indexes(disk1, disk2, addrs.drop_first());
            assert(addrs =~= seq![addrs[0]] + addrs.drop_first());
            assert(seq_indexes(xor(disk1, disk2), seq![addrs[0]] + addrs.drop_first()) =~=
                   seq![xor(disk1, disk2)[addrs[0]]] + seq_indexes(xor(disk1, disk2), addrs.drop_first()));
            assert(valid_index(disk1, addrs[0]));
        }
    }

    pub proof fn sum_permute(s1: Seq<nat>, s2: Seq<nat>)
        requires
            s1.to_multiset() == s2.to_multiset()
        ensures
            sum(s1) == sum(s2)
    {
        fold_right_permutation(s1, s2, |i, s: nat| { s+i as nat }, 0)
    }

    pub proof fn sum_concat(s1: Seq<nat>, s2: Seq<nat>)
        ensures
            sum(s1+s2) == sum(s1) + sum(s2)
    {
        let s = s1+s2;
        assert(s1 == s.subrange(0, s1.len() as int));
        assert(s2 == s.subrange(s1.len() as int, s.len() as int));
        s.lemma_fold_right_split(|i, s: nat| { s+i as nat }, 0, s1.len() as int);
        s1.lemma_fold_right_commute_one(sum(s2), |i, s: nat| { s+i as nat }, 0);
    }

    pub proof fn sum_remove(s: Seq<nat>, i: int)
        requires
            0 <= i < s.len()
        ensures
            sum(s) == s[i] + sum(s.remove(i))
    {
        let s1 = s.subrange(0, i);
        let s2 = s.subrange(i, s.len() as int);
        assert(s == s1+s2);

        assert(s.remove(i) == s1 + s2.drop_first());

        sum_concat(s1, s2);
        assert(sum(s) == sum(s1) + sum(s2));
        sum_concat(s1, s2.drop_first());
        assert(sum(s.remove(i)) == sum(s1) + sum(s2.drop_first()));

        s2.lemma_fold_right_alt(|i, s: nat| { s+i as nat }, 0);
        s2.drop_first().lemma_fold_right_alt(|i, s: nat| { s+i as nat }, 0);
        assert(sum(s2) == s2[0] + sum(s2.drop_first()));
    }

    pub proof fn sum_seq_indexes(s: Seq<nat>, indexes: Seq<int>)
        requires
            indexes.no_duplicates(),
            valid_indexes(s, indexes),
        ensures
            sum(seq_indexes(s, indexes)) <= sum(s)
    {
        indexes.lemma_sort_ensures();
        let indexes_sorted = indexes.sort();
        indexes.lemma_multiset_has_no_duplicates();
        indexes_sorted.lemma_multiset_has_no_duplicates_conv();
        valid_indexes_permute(s, indexes, indexes_sorted);
        sum_seq_indexes_helper(s, indexes_sorted);
        seq_indexes_permute(s, indexes, indexes_sorted);
        sum_permute(seq_indexes(s, indexes), seq_indexes(s, indexes_sorted));
    }

    pub proof fn sum_seq_indexes_helper(s: Seq<nat>, indexes: Seq<int>)
        requires
            indexes.no_duplicates(),
            valid_indexes(s, indexes),
            sorted_by(indexes, |x: int, y: int| x <= y),
        ensures
            sum(seq_indexes(s, indexes)) <= sum(s)
        decreases
            s.len()
    {
        if indexes.len() > 0 {
            let i = indexes.last();
            assert(valid_index(s, i));

            let s0 = s.subrange(0, i);
            let s1 = s.subrange(i, s.len() as int);
            assert(s == s0 + s1);

            sum_concat(s0, s1);
            assert(sum(s0) + sum(s1) == sum(s));

            seq_indexes_last(s, indexes);
            assert(seq_indexes(s, indexes) == seq_indexes(s, indexes.drop_last()).push(s[i]));
            assert(sorted_by(indexes.drop_last(), |x: int, y: int| x <= y));

            assert forall |j: int| 0 <= j < indexes.drop_last().len() implies #[trigger] valid_index(s0, indexes.drop_last()[j]) by {
                let idx = indexes.drop_last()[j];
                assert(valid_index(s, idx));
                assert(0 <= idx);
                assert((|x: int, y: int| x <= y)(indexes[j], indexes.last()));
            }
            sum_seq_indexes_helper(s0, indexes.drop_last());

            assert forall |j: int| 0 <= j < indexes.drop_last().len() implies 0 <= #[trigger] indexes.drop_last()[j] < s0.len() by {
                assert(valid_index(s0, indexes.drop_last()[j]));
            }

            seq_indexes_subrange(s, indexes.drop_last(), s0.len() as int);
            sum_concat(seq_indexes(s, indexes.drop_last()), seq![s[i]]);
            reveal_with_fuel(Seq::fold_right, 2);
            assert(sum(seq![s[i]]) == s[i]);

            assert(seq_indexes(s0, indexes.drop_last()) == seq_indexes(s, indexes.drop_last()));
            assert(seq_indexes(s, seq![i]) == seq![s[i]]);

            assert(sum(seq_indexes(s0, indexes.drop_last())) <= sum(s0));
            sum_remove(s1, 0);
            assert(sum(s1) == s1[0] + sum(s1.remove(0)));
            assert(sum(seq_indexes(s, seq![i])) <= sum(s1));

            assert(seq_indexes(s0, indexes.drop_last()) + seq_indexes(s, seq![i]) == seq_indexes(s, indexes));

            sum_concat(seq_indexes(s0, indexes.drop_last()), seq_indexes(s, seq![i]));
            assert(sum(seq_indexes(s0, indexes.drop_last())) + sum(seq_indexes(s, seq![i])) == sum(seq_indexes(s, indexes)));
        }
    }

    pub proof fn seq_popcnt_indexes(s: Seq<u8>, indexes: Seq<int>)
        requires
            valid_indexes(s, indexes)
        ensures
            seq_popcnt(seq_indexes(s, indexes)) =~= seq_indexes(seq_popcnt(s), indexes)
        decreases
            indexes.len()
    {
        if indexes.len() == 0 {
        } else {
            seq_popcnt_indexes(s, indexes.drop_first());
            seq_indexes_first(s, indexes);
            assert(seq_popcnt(seq![s[indexes[0]]] + seq_indexes(s, indexes.drop_first())) =~=
                   seq![popcnt_byte(s[indexes[0]])] + seq_popcnt(seq_indexes(s, indexes.drop_first())));
        }
    }

    pub open spec fn zeroes(len: nat) -> Seq<u8> {
        Seq::new(len, |i: int| 0)
    }

    pub proof fn sum_zeroes(len: nat)
        ensures
            sum(Seq::new(len, |i: int| 0nat)) == 0
        decreases
            len
    {
        if len > 0 {
            let l = Seq::new(len, |i: int| 0nat);
            let l1 = Seq::new((len-1) as nat, |i: int| 0nat);

            sum_zeroes(l1.len());
            assert(l1 == l.drop_last());
        }
    }

    pub proof fn popcnt_zeroes(len: nat)
        ensures
            popcnt(zeroes(len)) == 0
    {
        assert(popcnt_byte(0) == 0) by (bit_vector);
        assert(zeroes(len).map_values(|v: u8| popcnt_byte(v)) == Seq::new(len, |i: int| 0nat));
        sum_zeroes(len);
    }

    pub proof fn popcnt_seq_indexes(disk: Seq<u8>, addrs: Seq<int>)
        requires
            addrs.no_duplicates(),
            valid_indexes(disk, addrs),
        ensures
            popcnt(seq_indexes(disk, addrs)) <= popcnt(disk)
    {
        assert(forall |i: int| 0 <= i < addrs.len() ==> valid_index(disk, addrs[i]) ==> #[trigger] valid_index(seq_popcnt(disk), addrs[i]));
        sum_seq_indexes(seq_popcnt(disk), addrs);
        seq_popcnt_indexes(disk, addrs);
    }

    pub proof fn hamming_seq_indexes(disk1: Seq<u8>, disk2: Seq<u8>, addrs: Seq<int>)
        requires
            disk1.len() == disk2.len(),
            addrs.no_duplicates(),
            valid_indexes(disk1, addrs),
        ensures
            hamming(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs)) <= hamming(disk1, disk2),
    {
        assert(hamming(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs)) == popcnt(xor(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs))));
        xor_seq_indexes(disk1, disk2, addrs);
        assert(xor(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs)) ==
               seq_indexes(xor(disk1, disk2), addrs));
        assert(hamming(disk1, disk2) == popcnt(xor(disk1, disk2)));
        assert(forall |i: int| 0 <= i < addrs.len() ==> valid_index(disk1, addrs[i]) ==> #[trigger] valid_index(xor(disk1, disk2), addrs[i]));
        popcnt_seq_indexes(xor(disk1, disk2), addrs);
    }

    pub proof fn byte_xor_xor(a: u8, b: u8)
        ensures
            (a^b) ^ a == b,
    {
        assert((a^b) ^ a == b) by (bit_vector)
    }

    pub proof fn list_xor_xor(a: Seq<u8>, b: Seq<u8>)
        requires
            a.len() == b.len(),
        ensures
            xor(xor(a, b), a) == b,
        decreases
            a.len()
    {
        if a.len() == 0 {
            assert(xor(xor(a, b), a) == b)
        } else {
            byte_xor_xor(a[0], b[0]);
            list_xor_xor(a.drop_first(), b.drop_first());

            assert(a == seq![a[0]] + a.drop_first());
            assert(b == seq![b[0]] + b.drop_first());
            assert(xor(seq![a[0]] + a.drop_first(),
                       seq![b[0]] + b.drop_first()) ==
                   seq![a[0] ^ b[0]] +
                   xor(a.drop_first(), b.drop_first()));
            assert(xor(seq![a[0] ^ b[0]] + xor(a.drop_first(), b.drop_first()),
                       seq![a[0]] + a.drop_first()) ==
                   seq![(a[0] ^ b[0]) ^ a[0]] +
                   xor(xor(a.drop_first(), b.drop_first()),
                       a.drop_first()));

            // Q: how to search for verus lemmas?
        }
    }

    pub proof fn bytes_uncorrupted(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                   y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>,
                                   disk: Seq<u8>, corrupt: Seq<u8>)
        requires
            x_c.len() == x.len(),
            y == spec_crc64(x),
            y_c == spec_crc64(x_c),

            (x_addrs + y_addrs).no_duplicates(),
            corrupt.len() == disk.len(),
            valid_indexes(disk, x_addrs + y_addrs),

            x == seq_indexes(disk, x_addrs),
            x_c == seq_indexes(xor(disk, corrupt), x_addrs),
            y == seq_indexes(disk, y_addrs),
            y_c == seq_indexes(xor(disk, corrupt), y_addrs),
            popcnt(corrupt) < spec_crc64_hamming_bound((x+y).len()),
        ensures
            x == x_c
    {
        crc64_spec_len(x);
        crc64_spec_len(x_c);
        assert(forall |i: int| 0 <= i < (x_addrs + y_addrs).len() ==> valid_index(disk, (x_addrs + y_addrs)[i]) ==> #[trigger] valid_index(xor(disk, corrupt), (x_addrs + y_addrs)[i]));
        hamming_seq_indexes(xor(disk, corrupt), disk, x_addrs + y_addrs);
        list_xor_xor(disk, corrupt);
        assert(seq_indexes(xor(disk, corrupt), x_addrs + y_addrs) ==
               seq_indexes(xor(disk, corrupt), x_addrs) + seq_indexes(xor(disk, corrupt), y_addrs));
        assert(seq_indexes(disk, x_addrs + y_addrs) ==
               seq_indexes(disk, x_addrs) + seq_indexes(disk, y_addrs));
        crc64_hamming_bound_valid(x_c, x, y_c, y);
    }

    pub fn main() {
        // assert(popcnt(0) == 0);
        // assert(hamming_byte(0x00, 0x01) == 1);
        // assert(hamming(seq![0x00, 0x10, 0x08], seq![0x01, 0x10, 0x08]) == 1);

        let mut d = Disk::alloc(128, Ghost(0));
        d.write(5, 123);
        let v0 = d.read(5);
        let v1 = d.read(5);
        // assert(v0 == v1);

        // assert(corrupt0@@[5] == 0);
        // assert(v0 == 123 ^ corrupt0@@[5]);

        let v2 = d.read(5);
        // assert(v0 == v2);
    }
}
