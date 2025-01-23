use vstd::prelude::*;

verus! {
    pub trait ReadOperation : Sized {
        type Resource /* = () */;   // tracked resource(s) passed to callback
        type ExecResult /* = () */;

        spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool;
    }

    pub trait MutOperation : Sized {
        type Resource /* = () */;   // tracked resource(s) passed to callback
        type ExecResult /* = () */;

        spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool;
        spec fn ensures(self, pre: Self::Resource, post: Self::Resource) -> bool;
    }

    pub trait LinearizeRead<Op: ReadOperation> : Sized {
        type ApplyResult /* = () */;

        spec fn inv(self, op: Op) -> bool;

        open spec fn namespace(self) -> int {
            0
        }

        open spec fn post(self, r: Op::ExecResult, ar: Self::ApplyResult) -> bool {
            true
        }

        proof fn apply(tracked self, op: Op, tracked r: &Op::Resource, e: &Op::ExecResult) -> (tracked out: Self::ApplyResult)
            requires
                self.inv(op),
                op.requires(*r, *e),
            ensures
                self.post(*e, out),
            opens_invariants
                [ self.namespace() ];
    }

    pub trait LinearizeMut<Op: MutOperation> : Sized {
        type ApplyResult /* = () */;

        spec fn inv(self, op: Op) -> bool;

        open spec fn namespace(self) -> int {
            0
        }

        open spec fn post(self, r: Op::ExecResult, ar: Self::ApplyResult) -> bool {
            true
        }

        proof fn apply(tracked self, op: Op, tracked r: &mut Op::Resource, e: &Op::ExecResult) -> (tracked out: Self::ApplyResult)
            requires
                self.inv(op),
                op.requires(*old(r), *e),
            ensures
                op.ensures(*old(r), *r),
                self.post(*e, out),
            opens_invariants
                [ self.namespace() ];
    }
}
