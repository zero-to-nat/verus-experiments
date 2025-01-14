use vstd::prelude::*;
use super::disk::Disk;
use super::map_view::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<MapAuth<usize, u8>>,
    }

    type DiskView = MapFrac<usize, u8>;

    pub open spec fn seq_to_map<V>(off: nat, s: Seq<V>) -> Map<usize, V>
    {
        Map::new(|i: usize| off <= i < off + s.len(), |i: usize| s[i - off])
    }

    pub struct DiskAddr {
        pub addr: usize,
        pub len: Ghost<nat>,
        pub perm: Tracked<DiskView>,
    }

    impl DiskAddr {
        pub closed spec fn valid(self, id: int) -> bool
        {
            &&& self.perm@.valid(id)
            &&& self.perm@@.dom() == Set::<usize>::new(|i| self.addr <= i < self.addr + self.len@)
        }

        pub closed spec fn view(self) -> Seq<u8>
        {
            Seq::new(self.len@, |i| self.perm@@[(self.addr + i) as usize])
        }

        pub fn new(addr: usize, Ghost(len): Ghost<nat>, Tracked(perm): Tracked<DiskView>) -> (result: DiskAddr)
            requires
                perm.inv(),
                perm@.dom() =~= Set::<usize>::new(|i| addr <= i < addr + len),
            ensures
                result@ == Seq::new(len, |i| perm@[(addr + i) as usize]),
                result.valid(perm.id()),
        {
            DiskAddr{
                addr: addr,
                len: Ghost(len),
                perm: Tracked(perm),
            }
        }
    }

    impl DiskWrap {
        spec fn disk_matches_view(self, a: usize) -> bool
        {
            &&& self.a@@.contains_key(a) ==> a < self.d@.len()
            &&& self.a@@.contains_key(a) ==> self.d@[a as int] == self.a@@[a]
        }

        pub closed spec fn inv(self) -> bool
        {
            &&& self.d.inv()
            &&& self.a@.inv()
            &&& forall |a: usize| self.disk_matches_view(a)
        }

        pub closed spec fn id(self) -> int
        {
            self.a@.id()
        }

        pub fn read_one(&self, a: usize, Tracked(perm): Tracked<&DiskView>) -> (result: u8)
            requires
                self.inv(),
                perm.valid(self.id()),
                perm@.contains_key(a),
            ensures
                result == perm@[a]
        {
            proof {
                perm.agree(self.a.borrow());
            }
            assert(self.disk_matches_view(a));
            self.d.read_one(a)
        }

        pub fn write_one(&mut self, a: usize, v: u8, Tracked(perm): Tracked<&mut DiskView>)
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                old(perm)@.contains_key(a),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.valid(self.id()),
                perm@ =~= old(perm)@.insert(a, v),
        {
            proof {
                perm.agree(self.a.borrow());
            }
            assert(self.disk_matches_view(a));
            self.d.write_one(a, v);
            proof {
                perm.update(self.a.borrow_mut(), map![a => v]);
            }
            assert forall |x: usize| self.disk_matches_view(x) by {
                assert(old(self).disk_matches_view(x));
            }
        }

        pub fn read(&self, a: usize, len: usize, Tracked(perm): Tracked<&DiskView>) -> (result: Vec<u8>)
            requires
                self.inv(),
                perm.valid(self.id()),
                Set::<usize>::new(|i| a <= i < a + len) <= perm@.dom(),
            ensures
                result@ =~= Seq::new(len as nat, |i| perm@[(a + i) as usize]),
        {
            proof {
                perm.agree(self.a.borrow());
            }
            let r = self.d.read(a, len);
            assert(r@ =~= self.d@.subrange(a as int, a+len as nat));
            assert(self.d@.subrange(a as int, a+len as nat) =~= Seq::new(len as nat, |i| perm@[(a+i) as usize]));
            r
        }

        pub fn read_wrapped(&self, a: &DiskAddr, len: usize) -> (result: Vec<u8>)
            requires
                self.inv(),
                a.valid(self.id()),
                len == a@.len(),
            ensures
                result@ == a@,
        {
            self.read(a.addr, len, Tracked(a.perm.borrow()))
        }

        pub fn write(&mut self, a: usize, v: &[u8], Tracked(perm): Tracked<&mut DiskView>)
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                Set::<usize>::new(|i| a <= i < a + v@.len()) <= old(perm)@.dom(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.valid(self.id()),
                perm@ =~= old(perm)@.union_prefer_right(seq_to_map(a as nat, v@)),
        {
            proof {
                perm.agree(self.a.borrow());
            }
            self.d.write(a, v);
            proof {
                perm.update(self.a.borrow_mut(), seq_to_map(a as nat, v@));
            }
        }

        pub fn write_wrapped(&mut self, a: &mut DiskAddr, v: &[u8])
            requires
                old(self).inv(),
                old(a).valid(old(self).id()),
                old(a)@.len() == v@.len(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                a.valid(self.id()),
                a.addr == old(a).addr,
                a@ == v@,
        {
            self.write(a.addr, v, Tracked(a.perm.borrow_mut()));
        }

        pub fn new(d: Disk) -> (result: (DiskWrap, Tracked<DiskView>))
            requires
                d.inv(),
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id()),
                result.1@@ == seq_to_map(0, d@),
        {
            let tracked (ar, fr) = MapAuth::<usize, u8>::new(seq_to_map(0, d@));
            (DiskWrap{ d: d, a: Tracked(ar) }, Tracked(fr))
        }
    }
}
