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
        type ApplyHint /* = () */;  // when apply might otherwise be non-deterministic

        spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool;
        spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool;
    }

    pub trait ReadLinearizer<Op: ReadOperation> : Sized {
        type ApplyResult /* = () */;

        open spec fn namespace(self) -> int {
            0
        }

        open spec fn pre(self, op: Op) -> bool {
            true
        }

        open spec fn post(self, op: Op, r: Op::ExecResult, ar: Self::ApplyResult) -> bool {
            true
        }

        proof fn apply(tracked self, op: Op, tracked r: &Op::Resource, e: &Op::ExecResult) -> (tracked out: Self::ApplyResult)
            requires
                self.pre(op),
                op.requires(*r, *e),
            ensures
                self.post(op, *e, out),
            opens_invariants
                [ self.namespace() ];
    }

    pub trait MutLinearizer<Op: MutOperation> : Sized {
        type ApplyResult /* = () */;

        open spec fn namespace(self) -> int {
            0
        }

        open spec fn pre(self, op: Op) -> bool {
            true
        }

        open spec fn post(self, op: Op, r: Op::ExecResult, ar: Self::ApplyResult) -> bool {
            true
        }

        proof fn apply(tracked self, op: Op, hint: Op::ApplyHint, tracked r: &mut Op::Resource, e: &Op::ExecResult) -> (tracked out: Self::ApplyResult)
            requires
                self.pre(op),
                op.requires(hint, *old(r), *e),
            ensures
                op.ensures(hint, *old(r), *r),
                self.post(op, *e, out),
            opens_invariants
                [ self.namespace() ];
    }
}
