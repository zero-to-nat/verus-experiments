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

    pub open spec fn popcnt(l: Seq<u8>) -> nat {
        sum(l.map_values(|v: u8| popcnt_byte(v)))
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

    // This proof function is marked verifier::external_body to assume that the
    // CRC64 function, as captured by spec_crc64(), correctly achieves the hamming
    // bounds described in spec_crc64_hamming_bound.
    #[verifier::external_body]
    pub proof fn crc64_hamming_bound_valid(bytes1: Seq<u8>, bytes2: Seq<u8>, crc1: Seq<u8>, crc2: Seq<u8>)
        requires
            crc1 == spec_crc64(bytes1),
            crc2 == spec_crc64(bytes2),
            (bytes1 + crc1).len() == (bytes2 + crc2).len(),
            hamming(bytes1 + crc1, bytes2 + crc2) <= spec_crc64_hamming_bound((bytes1 + crc1).len()),
        ensures
            bytes1 == bytes2,
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
