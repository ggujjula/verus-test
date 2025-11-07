use vstd::prelude::*;

verus! {

spec fn add_two_spec(x: int, y: int) -> int
{
    x+y
}

fn add_two(x: u64, y: u64) -> (z: u64)
    requires x < u64::MAX / 2, y < u64::MAX / 2,
    ensures z == add_two_spec(x as int, y as int)
{
    x + y
}

}
