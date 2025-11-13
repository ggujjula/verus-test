use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::relations::sorted_by;

verus! {

pub fn insertion_sort(mut v: Vec<u64>) -> (out: Vec<u64>)
    ensures
        v@.to_multiset() =~= out@.to_multiset(),
        sorted_by(out@, |a: u64, b: u64| a <= b),
{
    if v.len() <= 1 {
        return v;
    }
    let ghost start_vec = v@;
    let ghost s_ms = start_vec.to_multiset();
    let mut index = 0;
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            0 <= index < v.len(),
            forall |j: int| 0 <= j < i ==> v[index as int] <= v[j as int]
        decreases v.len() - i
    {
        if v[i] <= v[index] {
            index = i;
        }
        i += 1;
    }
    let elem = v.remove(index);
    let mut out = vec![elem];
    proof {
        start_vec.to_multiset_ensures();
        v@.to_multiset_ensures();
        out@.to_multiset_ensures();
    }
    while v.len() > 0
        invariant
            v.len() >= 0,
            sorted_by(out@, |a: u64, b: u64| a <= b),
            out@.len() >= 1,
            forall |i: int| 0 <= i < v@.len() ==> out@[out@.len() - 1] <= #[trigger] v@[i],
            s_ms =~= v@.to_multiset().add(out@.to_multiset()),
        decreases v.len(),
    {
        proof {
            out@.to_multiset_ensures();
            v@.to_multiset_ensures();
        }
        assert(forall |i: int, j: int| 0 <= i < j < out@.len() ==> (|a: u64, b:u64| a <= b)(out@[i],out@[j]));
        let mut index = 0;
        let mut i = 1;
        while i < v.len()
            invariant
                1 <= i <= v.len(),
                0 <= index < v.len(),
                forall |j: int| 0 <= j < i ==> v[index as int] <= v[j as int]
            decreases v.len() - i
        {
            if v[i] <= v[index] {
                index = i;
            }
            i += 1;
        }
        let elem = v.remove(index);
        out.push(elem);
    }
    proof!(v@.to_multiset_ensures());
    out
}

}
