use vstd::prelude::*;
use super::map_view::*;

verus! {
    pub struct SeqAuth<V> {
        ghost len: nat,
        auth: MapAuth<int, V>,
    }

    pub struct SeqFrac<V> {
        ghost off: nat,
        ghost len: nat,
        frac: MapFrac<int, V>,
    }

    impl<V> SeqAuth<V> {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.auth.inv()
            &&& self.auth@.dom() =~= Set::new(|i: int| 0 <= i < self.len)
        }

        pub closed spec fn id(self) -> int
        {
            self.auth.id()
        }

        pub closed spec fn view(self) -> Seq<V>
        {
            Seq::new(self.len, |i: int| self.auth@[i])
        }

        pub proof fn new(s: Seq<V>) -> (tracked result: (SeqAuth<V>, SeqFrac<V>))
            requires
                s.len() > 0,
            ensures
                result.0.inv(),
                result.0@ =~= s,
                result.1.valid(result.0.id()),
                result.1.off() == 0,
                result.1@ =~= s,
        {
            let tracked (mauth, mfrac) = MapAuth::<int, V>::new(Map::new(|i| 0 <= i < s.len(), |i: int| s[i]));
            let tracked auth = SeqAuth{
                len: s.len(),
                auth: mauth,
            };
            let tracked frac = SeqFrac{
                off: 0,
                len: s.len(),
                frac: mfrac,
            };
            (auth, frac)
        }
    }

    impl<V> SeqFrac<V> {
        pub open spec fn valid(self, id: int) -> bool
        {
            &&& self.id() == id
            &&& self.inv()
        }

        pub closed spec fn inv(self) -> bool
        {
            &&& self.frac.inv()
            &&& self.frac@.dom() =~= Set::new(|i: int| self.off <= i < self.off + self.len)
            &&& self.len > 0
        }

        pub closed spec fn view(self) -> Seq<V>
        {
            Seq::new(self.len, |i: int| self.frac@[self.off + i])
        }

        pub closed spec fn off(self) -> nat
        {
            self.off
        }

        pub closed spec fn id(self) -> int
        {
            self.frac.id()
        }

        pub proof fn agree(tracked self: &SeqFrac<V>, tracked auth: &SeqAuth<V>)
            requires
                self.valid(auth.id()),
                auth.inv(),
            ensures
                self@ =~= auth@.subrange(self.off() as int, self.off() + self@.len() as int),
                self@.len() > 0,
                self.off() + self@.len() <= auth@.len(),
        {
            self.frac.agree(&auth.auth);

            assert(self.frac@.contains_key(self.off + self.len - 1));
            assert(auth.auth@.contains_key(self.off + self.len - 1));
            assert(self.off + self.len - 1 < auth@.len());

            assert forall|i: int| 0 <= i < self.len implies #[trigger] self.frac@[self.off + i] == auth@[self.off + i] by {
                assert(self.frac@.contains_key(self.off + i));
                assert(auth.auth@.contains_key(self.off + i));
            };
        }

        pub proof fn agree_map(tracked self: &SeqFrac<V>, tracked auth: &MapAuth<int, V>)
            requires
                self.valid(auth.id()),
                auth.inv(),
            ensures
                self@.len() > 0,
                forall |i| 0 <= i < self@.len() ==> #[trigger] auth@.contains_key(self.off() + i) && auth@[self.off() + i] == self@[i],
        {
            self.frac.agree(&auth);

            assert forall |i: int| 0 <= i < self.len implies #[trigger] auth@.contains_key(self.off + i) && self.frac@[self.off + i] == auth@[self.off + i] by {
                assert(self.frac@.contains_key(self.off + i));
            };
        }

        pub proof fn update(tracked self: &mut SeqFrac<V>, tracked auth: &mut SeqAuth<V>, v: Seq<V>)
            requires
                old(self).valid(old(auth).id()),
                old(auth).inv(),
                v.len() == old(self)@.len(),
            ensures
                self.valid(auth.id()),
                self.off() == old(self).off(),
                auth.inv(),
                auth.id() == old(auth).id(),
                self@ =~= v,
                auth@ =~= Seq::new(old(auth)@.len(), |i: int| if self.off() <= i < self.off() + v.len() { v[i - self.off()] } else { old(auth)@[i] }),
        {
            self.update_map(&mut auth.auth, v);
        }

        pub proof fn update_map(tracked self: &mut SeqFrac<V>, tracked auth: &mut MapAuth<int, V>, v: Seq<V>)
            requires
                old(self).valid(old(auth).id()),
                old(auth).inv(),
                v.len() == old(self)@.len(),
            ensures
                self.valid(auth.id()),
                self.off() == old(self).off(),
                auth.inv(),
                auth.id() == old(auth).id(),
                self@ =~= v,
                auth@ =~= Map::new(|i: int| old(auth)@.contains_key(i),
                                   |i: int| if self.off() <= i < self.off() + v.len() { v[i - self.off()] } else { old(auth)@[i] }),
        {
            let vmap = Map::new(|i| self.off <= i < self.off + self.len, |i: int| v[i - self.off]);
            self.frac.agree(auth);
            self.frac.update(auth, vmap);
        }

        pub proof fn split(tracked self: &mut SeqFrac<V>, n: int) -> (tracked result: SeqFrac<V>)
            requires
                old(self).inv(),
                0 < n < old(self)@.len(),
            ensures
                self.inv(),
                result.inv(),
                self.id() == old(self).id(),
                self.off() == old(self).off(),
                result.id() == self.id(),
                result.off() == old(self).off() + n,
                self@ =~= old(self)@.subrange(0, n),
                result@ =~= old(self)@.subrange(n, old(self)@.len() as int),
        {
            let tracked mfrac = self.frac.split(Set::new(|i: int| self.off + n <= i < self.off + self.len));
            let tracked result = SeqFrac{
                off: (self.off + n) as nat,
                len: (self.len - n) as nat,
                frac: mfrac,
            };

            self.len = n as nat;
            result
        }

        pub proof fn combine(tracked self: &mut SeqFrac<V>, tracked r: SeqFrac<V>)
            requires
                old(self).inv(),
                r.valid(old(self).id()),
                r.off() == old(self).off() + old(self)@.len(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ =~= old(self)@ + r@,
        {
            self.frac.combine(r.frac);
            self.len = self.len + r.len;
        }

        // Helper to lift MapFrac's into SeqFrac's.
        pub proof fn new(off: nat, len: nat, tracked f: MapFrac<int, V>) -> (tracked result: SeqFrac<V>)
            requires
                len > 0,
                f.inv(),
                f@.dom() == Set::new(|i: int| off <= i < off + len),
            ensures
                result.valid(f.id()),
                result.off() == off,
                result@ == Seq::new(len, |i| f@[off + i]),
        {
            SeqFrac{
                off: off, len: len, frac: f,
            }
        }
    }
}
