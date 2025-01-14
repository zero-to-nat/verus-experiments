use vstd::prelude::*;
use super::disk::Disk;
use super::map_view::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<MapAuth<usize, u8>>,
    }

    type DiskView = MapFrac<usize, u8>;

    pub open spec fn seq_to_map<V>(s: Seq<V>) -> Map<usize, V>
    {
        Map::new(|i: usize| i < s.len(), |i: usize| s[i as int])
    }

    pub struct DiskAddr {
        addr: usize,
        len: Ghost<nat>,
        perm: Tracked<DiskView>,
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
            &&& self.a@.inv()
            &&& forall |a: usize| self.disk_matches_view(a)
        }

        pub closed spec fn id(self) -> int
        {
            self.a@.id()
        }

        pub fn read(&self, a: usize, Tracked(perm): Tracked<&DiskView>) -> (result: u8)
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
            self.d.read(a)
        }

        pub fn write(&mut self, a: usize, v: u8, Tracked(perm): Tracked<&mut DiskView>)
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
            self.d.write(a, v);
            proof {
                perm.update(self.a.borrow_mut(), map![a => v]);
            }
            assert forall |x: usize| self.disk_matches_view(x) by {
                assert(old(self).disk_matches_view(x));
            }
        }

        pub fn new(d: Disk) -> (result: (DiskWrap, Tracked<DiskView>))
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id()),
                result.1@@ == seq_to_map(d@),
        {
            let tracked (ar, fr) = MapAuth::<usize, u8>::new(seq_to_map(d@));
            (DiskWrap{ d: d, a: Tracked(ar) }, Tracked(fr))
        }
    }
}
