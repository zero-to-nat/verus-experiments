use builtin::*;
use vstd::prelude::*;

verus! {
// copied from demo2

pub trait CallBackSemantics : Sized{
    type Param;         // input of call back (ghost resource)
    type GhostResult;   // output of call back (e.g. fractional resource)
    type ExecResult;

    spec fn requires(id: int, p: Self::Param, e: Self::ExecResult) -> bool
    ;

    spec fn ensures(id: int, p: Self::Param, e: Self::GhostResult) -> bool
    ;
}

pub trait GenericCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), p, *e),
    ensures
        S::ensures(self.id(), p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

// NOTE: the only difference is the param type in the callback proof fn
// this is needed to untie the lifetime of the param from the callback struct
pub trait GenericReadCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: &S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), *p, *e),
    ensures
        S::ensures(self.id(), *p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

// NOTE: a workaround for opens_invariants not taking a set of namespaces
// does not open other_namespace
pub trait GenericSingleInvCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), p, *e),
    ensures
        S::ensures(self.id(), p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

// NOTE: the only difference is the param type in the callback proof fn
// this is needed to untie the lifetime of the param from the callback struct
pub trait GenericSingleInvReadCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: &S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), *p, *e),
    ensures
        S::ensures(self.id(), *p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

}