use vstd::prelude::*;
use vstd::bytes::*;

mod hamming;

use hamming::*;

verus! {
    pub open spec fn spec_crc64_bytes(bytes: Seq<u8>) -> Seq<u8> {
        spec_u64_to_le_bytes(spec_crc64_u64(bytes))
    }

    pub closed spec fn spec_crc64_u64(bytes: Seq<u8>) -> u64;

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
            out@ == spec_crc64_bytes(bytes@),
    {
        Vec::new()
    }

    // This proof function is marked verifier::external_body to assume that all
    // CRC-64 values are 8 bytes long.
    #[verifier::external_body]
    pub proof fn crc64_spec_len()
        ensures
            forall |bytes| (#[trigger] spec_crc64_bytes(bytes)).len() == 8,
    {}

    // This proof function is marked verifier::external_body to assume that the
    // CRC64 function, as captured by spec_crc64(), correctly achieves the hamming
    // bounds described in spec_crc64_hamming_bound.
    #[verifier::external_body]
    pub proof fn crc64_hamming_bound_valid(bytes1: Seq<u8>, bytes2: Seq<u8>, crc1: Seq<u8>, crc2: Seq<u8>)
        requires
            crc1 == spec_crc64_bytes(bytes1),
            crc2 == spec_crc64_bytes(bytes2),
            (bytes1 + crc1).len() == (bytes2 + crc2).len(),
        ensures
            bytes1 == bytes2 ||
            hamming(bytes1 + crc1, bytes2 + crc2) >= spec_crc64_hamming_bound((bytes1 + crc1).len())
    {}

    pub proof fn bytes_uncorrupted(x_c: Seq<u8>, x: Seq<u8>, x_addrs: Seq<int>,
                                   y_c: Seq<u8>, y: Seq<u8>, y_addrs: Seq<int>,
                                   disk: Seq<u8>, corrupt: Seq<u8>)
        requires
            x_c.len() == x.len(),
            y == spec_crc64_bytes(x),
            y_c == spec_crc64_bytes(x_c),

            (x_addrs + y_addrs).no_duplicates(),
            corrupt.len() == disk.len(),
            valid_indexes(disk, x_addrs + y_addrs),

            x == S(disk)[x_addrs],
            x_c == S(xor(disk, corrupt))[x_addrs],
            y == S(disk)[y_addrs],
            y_c == S(xor(disk, corrupt))[y_addrs],
            popcnt(corrupt) < spec_crc64_hamming_bound((x+y).len()),
        ensures
            x == x_c
    {
        assert(forall |i: int| 0 <= i < (x_addrs + y_addrs).len() ==> valid_index(disk, (x_addrs + y_addrs)[i]) ==> #[trigger] valid_index(xor(disk, corrupt), (x_addrs + y_addrs)[i]));
        hamming_indexes(xor(disk, corrupt), disk, x_addrs + y_addrs);
        list_xor_xor(disk, corrupt);
        assert(S(xor(disk, corrupt))[x_addrs + y_addrs] =~=
               S(xor(disk, corrupt))[x_addrs] + S(xor(disk, corrupt))[y_addrs]);
        assert(S(disk)[x_addrs + y_addrs] =~= S(disk)[x_addrs] + S(disk)[y_addrs]);
        crc64_hamming_bound_valid(x_c, x, y_c, y);
    }

    // Disk that provides Hamming-style corruption guarantees.
    pub struct HammingDisk {
        data: Ghost<Seq<u8>>,
        corruption: Ghost<Seq<u8>>,
        corruption_bits: Ghost<nat>,
    }

    impl HammingDisk {
        pub closed spec fn view(&self) -> Seq<u8> { self.data@ }
        pub closed spec fn corrupt(&self) -> Seq<u8> { self.corruption@ }
        pub closed spec fn corrupt_bits(&self) -> nat { self.corruption_bits@ }

        pub open spec fn inv(&self) -> bool {
            self@.len() == self.corrupt().len() &&
            popcnt(self.corrupt()) <= self.corrupt_bits()
        }

        pub fn alloc(len: u64, Ghost(max_corrupt): Ghost<nat>) -> (res: Self)
            ensures
                res.inv(),
                res@.len() == len,
                res.corrupt_bits() == max_corrupt,
        {
            let ghost disk = Seq::new(len as nat, |i: int| 0);

            // prove that there exists a Seq<u8> with a suitably low popcnt value
            assert(exists |s: Seq<u8>| #[trigger] s.len() == len && popcnt(s) <= max_corrupt) by {
                popcnt_u8_zeroes(len as nat);
            };

            let ghost corrupt = choose |s: Seq<u8>| #[trigger] s.len() == len && popcnt(s) <= max_corrupt;
            Self{
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
        pub fn write_range(&mut self, addr: u64, bytes: &[u8])
            requires
                old(self).inv(),
                addr + bytes@.len() <= old(self)@.len(),
            ensures
                self.inv(),
                self@ == old(self)@.map(|pos: int, pre_byte: u8| if addr <= pos < addr + bytes@.len() { bytes@[pos-addr] } else { pre_byte }),
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

        #[verifier::external_body]
        pub fn read_range(&self, addr: u64, count: u64) -> (res: (Vec<u8>, Ghost<Seq<u8>>))
            requires
                self.inv(),
                addr + count <= self@.len(),
            ensures
                res.1@.len() == self@.len(),
                res.0@ == xor(self@, and(res.1@, self.corrupt())).subrange(addr as int, addr+count),
        {
            unimplemented!()
        }
    }

    // This is also unproven in storage_node/src/pmem/pmemspec_t.rs..
    #[verifier::external_body]
    pub exec fn crc_equal(crc1: &[u8], crc2: &[u8]) -> bool
        requires
            crc1.len() == 8,
            crc2.len() == 8,
        returns
            crc1@ == crc2@
    {
        let crc1_u64 = u64_from_le_bytes(crc1);
        let crc2_u64 = u64_from_le_bytes(crc2);
        crc1_u64 == crc2_u64
    }

    pub fn main() {
        // assert(popcnt(0) == 0);
        // assert(hamming_byte(0x00, 0x01) == 1);
        // assert(hamming(seq![0x00, 0x10, 0x08], seq![0x01, 0x10, 0x08]) == 1);

        let mut d0 = HammingDisk::alloc(128, Ghost(0));
        d0.write(5, 123);
        assert(d0@[5] == 123);
        let (v0, Ghost(mask0)) = d0.read_range(5, 1);
        assert(v0@[0] == xor(d0@, and(mask0, d0.corrupt()))[5]);
        proof {
            popcnt_and(mask0, d0.corrupt());
            xor_zeroes(d0@, and(mask0, d0.corrupt()));
        }
        assert(v0@[0] == d0@[5]);

        let mut d1 = HammingDisk::alloc(128, Ghost(1));
        let buf = vec![123, 124, 125, 126];
        let crc = crc64(buf.as_slice());
        proof {
            crc64_spec_len();
        }
        d1.write_range(10, buf.as_slice());
        d1.write_range(20, crc.as_slice());
        assert(buf@ == d1@.subrange(10, 14));
        assert(crc@ == d1@.subrange(20, 28));
        let (bufR, Ghost(mask1)) = d1.read_range(10, 4);
        let (crcR, Ghost(mask2)) = d1.read_range(20, 8);

        assert(bufR@ == xor(d1@, and(mask1, d1.corrupt())).subrange(10, 14));
        assert(crcR@ == xor(d1@, and(mask2, d1.corrupt())).subrange(20, 28));

        let crc2 = crc64(bufR.as_slice());
        if crc_equal(crcR.as_slice(), crc2.as_slice()) {
            proof {
                let buf_addrs = seq![10, 11, 12, 13];
                let crc_addrs = seq![20, 21, 22, 23, 24, 25, 26, 27];
                assert(buf@ == S(d1@)[buf_addrs]);
                assert(crc@ == S(d1@)[crc_addrs]);
                assert(bufR@ == S(xor(d1@, d1.corrupt()))[buf_addrs]);
                assert(crcR@ == S(xor(d1@, d1.corrupt()))[crc_addrs]);
                bytes_uncorrupted(bufR@, buf@, buf_addrs,
                                  crcR@, crc@, crc_addrs,
                                  d1@, d1.corrupt());
            }
            assert(bufR@ == buf@);
        }

        // proof {
        //     popcnt_and(mask1, d1.corrupt());
        //     xor_zeroes(d1@, and(mask1, d1.corrupt()));
        // }
        // assert(v1@[0] == d1@[5]);
    }
}
