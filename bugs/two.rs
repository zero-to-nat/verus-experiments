vstd::prelude::verus! {

proof fn f() {
    Tracked(()).borrow();
}

} // verus!
