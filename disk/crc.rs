use vstd::prelude::*;

verus! {
    pub open spec fn one_if(a: u8) -> nat {
        if a == 0 { 0 } else { 1 }
    }

    pub open spec fn popcnt_byte(a: u8) -> nat {
        one_if(a&0x80) + one_if(a&0x40) + one_if(a&0x20) + one_if(a&0x10) +
        one_if(a&0x08) + one_if(a&0x04) + one_if(a&0x02) + one_if(a&0x01)
    }

    pub open spec fn sum(l: Seq<nat>) -> nat {
        l.fold_left(0, |s: nat, i| { s+i as nat })
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
        if len <= 32768 {
            8
        } else if len <= 32768 {
            7
        } else if len <= 126701 {
            6
        } else if len <= 126701 {
            5
        } else if len <= 8589606850 {
            4
        } else if len <= 8589606850 {
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
        ghost data: Seq<u8>,
    }

    pub struct DiskCorruption {
        ghost v: Seq<u8>,
        ghost max_bits: nat,
    }

    impl DiskCorruption {
        pub closed spec fn view(&self) -> Seq<u8> { self.v }
        pub closed spec fn max_bits(&self) -> nat { self.max_bits }

        #[verifier::external_body]
        pub proof fn alloc(len: nat, max_bits: nat) -> (tracked res: DiskCorruption)
            ensures
                res@.len() == len,
                res.max_bits() == max_bits,
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub proof fn validate(&self)
            ensures
                popcnt(self@) <= self.max_bits(),
        {}

        #[verifier::external_body]
        pub proof fn refresh(tracked self) -> (tracked res: DiskCorruption)
            ensures
                res@.len() == self@.len(),
                res.max_bits() == self.max_bits(),
        {
            unimplemented!()
        }
    }

    impl Disk {
        pub closed spec fn view(&self) -> Seq<u8> { self.data }
        pub closed spec fn inv(&self) -> bool;

        #[verifier::external_body]
        pub fn alloc(len: u64) -> (res: Disk)
            ensures
                res.inv(),
                res@.len() == len,
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub fn write(&mut self, addr: u64, val: u8)
            requires
                old(self).inv(),
                addr < old(self)@.len(),
            ensures
                self.inv(),
                self@ == old(self)@.update(addr as int, val),
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub fn read(&self, addr: u64, Tracked(corrupt): &Tracked<DiskCorruption>) -> (res: u8)
            requires
                self.inv(),
                addr < self@.len(),
                corrupt@.len() == self@.len(),
            ensures
                res == self@[addr as int] ^ corrupt@[addr as int],
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
            seq_indexes(s, indexes) == seq![s[indexes[0]]] + seq_indexes(s, indexes.drop_first())
    {
        assert(valid_index(s, indexes[0]));
        assert(indexes == seq![indexes[0]] + indexes.drop_first());
        assert(seq_indexes(s, seq![indexes[0]] + indexes.drop_first()) ==
               seq![s[indexes[0]]] + seq_indexes(s, indexes.drop_first()));
    }

    pub open spec fn valid_index<T>(s: Seq<T>, i: int) -> bool {
        0 <= i < s.len()
    }

    pub open spec fn valid_indexes<T>(s: Seq<T>, indexes: Seq<int>) -> bool {
        forall |i: int| 0 <= i < indexes.len() ==> #[trigger] valid_index(s, indexes[i])
    }

    pub proof fn xor_seq_indexes(disk1: Seq<u8>, disk2: Seq<u8>, addrs: Seq<int>)
        requires
            disk1.len() == disk2.len(),
            valid_indexes(disk1, addrs),
        ensures
            xor(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs)) == seq_indexes(xor(disk1, disk2), addrs)
        decreases
            addrs.len()
    {
        if addrs.len() == 0 {
            assert(xor(seq_indexes(disk1, addrs), seq_indexes(disk2, addrs)) == seq_indexes(xor(disk1, disk2), addrs))
        } else {
            xor_seq_indexes(disk1, disk2, addrs.drop_first());
            assert(addrs == seq![addrs[0]] + addrs.drop_first());
            assert(seq_indexes(disk1, seq![addrs[0]] + addrs.drop_first()) ==
                   seq![disk1[addrs[0]]] + seq_indexes(disk1, addrs.drop_first()));
            assert(seq_indexes(disk2, seq![addrs[0]] + addrs.drop_first()) ==
                   seq![disk2[addrs[0]]] + seq_indexes(disk2, addrs.drop_first()));
            assert(seq_indexes(xor(disk1, disk2), seq![addrs[0]] + addrs.drop_first()) ==
                   seq![xor(disk1, disk2)[addrs[0]]] + seq_indexes(xor(disk1, disk2), addrs.drop_first()));
            assert(xor(seq![disk1[addrs[0]]] + seq_indexes(disk1, addrs.drop_first()),
                       seq![disk2[addrs[0]]] + seq_indexes(disk2, addrs.drop_first())) ==
                   seq![disk1[addrs[0]] ^ disk2[addrs[0]]] +
                   xor(seq_indexes(disk1, addrs.drop_first()),
                       seq_indexes(disk2, addrs.drop_first())));
            assert(valid_index(disk1, addrs[0]));
        }
    }

    // Proof TBD.
    #[verifier::external_body]
    pub proof fn sum_seq_indexes(s: Seq<nat>, indexes: Seq<int>)
        requires
            indexes.no_duplicates(),
            valid_indexes(s, indexes),
        ensures
            sum(seq_indexes(s, indexes)) <= sum(s)
    {
    }

    pub proof fn seq_popcnt_indexes(s: Seq<u8>, indexes: Seq<int>)
        requires
            valid_indexes(s, indexes)
        ensures
            seq_popcnt(seq_indexes(s, indexes)) == seq_indexes(seq_popcnt(s), indexes)
        decreases
            indexes.len()
    {
        if indexes.len() == 0 {
            assert(seq_popcnt(seq_indexes(s, indexes)) == seq_indexes(seq_popcnt(s), indexes))
        } else {
            seq_popcnt_indexes(s, indexes.drop_first());
            seq_indexes_first(s, indexes);
            assert(valid_index(s, indexes[0]));
            assert(seq_popcnt(seq![s[indexes[0]]] + seq_indexes(s, indexes.drop_first())) ==
                   seq![popcnt_byte(s[indexes[0]])] + seq_popcnt(seq_indexes(s, indexes.drop_first())));
            assert(seq_popcnt(seq_indexes(s, indexes)) ==
                   seq_popcnt(seq![s[indexes[0]]] + seq_indexes(s, indexes.drop_first())));
            assert(seq![popcnt_byte(s[indexes[0]])] + seq_popcnt(seq_indexes(s, indexes.drop_first())) ==
                   seq_indexes(seq_popcnt(s), indexes));
        }
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

        let mut d = Disk::alloc(128);
        d.write(5, 123);
        let corrupt0 = Tracked(DiskCorruption::alloc(d@.len(), 0));
        let v0 = d.read(5, &corrupt0);
        let v1 = d.read(5, &corrupt0);
        assert(v0 == v1);

        // assert(corrupt0@@[5] == 0);
        // assert(v0 == 123 ^ corrupt0@@[5]);

        let corrupt1 = Tracked(corrupt0.get().refresh());
        let v2 = d.read(5, &corrupt1);
        // assert(v0 == v2);
    }
}
