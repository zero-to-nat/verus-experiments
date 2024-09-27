vstd::prelude::verus! {

pub trait Trait<T> {
    spec fn ok(r: T) -> bool;

    proof fn apply() -> (result: T)
        ensures
            Self::ok(result),
    ;
}

pub struct S {}

impl Trait<()> for S {
    open spec fn ok(r: ()) -> bool {
        true
    }

    proof fn apply() -> (result: ()) {
    }
}

} // verus!
