use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::relations::{
    antisymmetric, reflexive, sorted_by, strongly_connected, total_ordering, transitive,
};

verus! {

proof fn vec_add_eq_multiset_add<T>(v1: Seq<T>, v2: Seq<T>)
    ensures v1.to_multiset().add(v2.to_multiset()) =~= (v1 + v2).to_multiset(),
    decreases v2.len(),
{
    if v2.len() == 0 {
        v2.to_multiset_ensures();
        assert(v2.to_multiset() =~= Multiset::empty());
        assert(v1.to_multiset().add(v2.to_multiset()) =~= (v1 + v2).to_multiset());
    } else {
        let v1_ms = v1.to_multiset();
        let v2_small = v2.drop_last();
        let v2_s_ms = v2_small.to_multiset();
        let elem = v2.last();

        vec_add_eq_multiset_add(v1, v2_small);
        v2_small.to_multiset_ensures();
        (v1 + v2_small).to_multiset_ensures();
        assert(v1_ms.add(v2_s_ms).insert(elem) =~= v1_ms.add(v2_small.push(elem).to_multiset()));
        assert((v1 + v2_small).to_multiset().insert(elem) =~= ((v1 + v2_small).push(elem)).to_multiset());
        assert(v2 =~= v2_small.push(elem));
    }
}


fn merge<T>(mut v1: Vec<T>, mut v2: Vec<T>, sort_fn: impl Fn(&T, &T) -> bool, Ghost(ghost_fn): Ghost<spec_fn(T, T) -> bool>) -> (out: Vec<T>)
    requires
        forall |x: T, y: T| #[trigger] (call_requires(sort_fn, (&x, &y))),
        forall |x: T, y: T, r: bool| #[trigger] call_ensures(sort_fn, (&x, &y), r) ==> r == ghost_fn(x, y),
        total_ordering(ghost_fn),
        sorted_by(v1@, ghost_fn),
        sorted_by(v2@, ghost_fn),
    ensures
        out@.to_multiset() =~= v1@.to_multiset().add(v2@.to_multiset()),
        sorted_by(out@, ghost_fn),
{
    let ghost g_v1 = v1@;
    let ghost g_v2 = v2@;
    let ghost g_v = g_v1 + g_v2;
    let ghost g_ms = g_v.to_multiset();
    let mut out = vec![];
    assert(sorted_by(out@, ghost_fn));
    proof {
        out@.to_multiset_ensures();
        g_v1.to_multiset_ensures();
        g_v2.to_multiset_ensures();
        v1@.to_multiset_ensures();
        v2@.to_multiset_ensures();
        g_v.to_multiset_ensures();
    }
    assert(out@.to_multiset() == Multiset::<T>::empty());
    assert(g_v1.to_multiset().add(g_v2.to_multiset()) =~= g_ms) by {vec_add_eq_multiset_add(g_v1, g_v2)};
    assert(out@.to_multiset().add(v1@.to_multiset()).add(v2@.to_multiset()) =~= g_ms);
    #[verifier::loop_isolation(false)]
    while v1.len() > 0 || v2.len() > 0
        invariant
            v1.len() >= 0,
            v2.len() >= 0,
            sorted_by(out@, ghost_fn),
            sorted_by(v1@, ghost_fn),
            sorted_by(v2@, ghost_fn),
            forall |x: T, y: T| out@.contains(x) ==> v1@.contains(y) ==> #[trigger] ghost_fn(x, y),
            forall |x: T, y: T| out@.contains(x) ==> v2@.contains(y) ==> #[trigger] ghost_fn(x, y),
            out@.to_multiset().add(v1@.to_multiset()).add(v2@.to_multiset()) =~= g_ms,
        decreases
            v1.len() + v2.len(),
    {
        proof!(out@.to_multiset_ensures());
        proof!(v1@.to_multiset_ensures());
        proof!(v2@.to_multiset_ensures());
        if v1.len() == 0 {
            assert(v2.len() > 0);
            let elem = v2.remove(0);
            out.push(elem);
            assert(out@.to_multiset().add(v1@.to_multiset()).add(v2@.to_multiset()) =~= g_ms) by {
                out@.to_multiset_ensures();
                v1@.to_multiset_ensures();
                v2@.to_multiset_ensures();
                g_v.to_multiset_ensures();
            };
        } else if v2.len() == 0 {
            assert(v1.len() > 0);
            let elem = v1.remove(0);
            out.push(elem);
            assert(out@.to_multiset().add(v1@.to_multiset()).add(v2@.to_multiset()) =~= g_ms) by {
                out@.to_multiset_ensures();
                v1@.to_multiset_ensures();
                v2@.to_multiset_ensures();
                g_v.to_multiset_ensures();
            };
        } else {
            let elem = match sort_fn(&v1[0], &v2[0]) {
                true => {
                    let e = v1.remove(0);
                    assert(forall | j: int | 0 < j < v2@.len() ==> ghost_fn(e, v2@[0]) && ghost_fn(v2@[0],v2@[j]) ==> #[trigger] ghost_fn(e, v2@[j]));
                    assert(forall | j: int | 0 <= j < v2@.len() ==> ghost_fn(e, v2@[j]));
                    e
                }
                false =>  {
                    let e = v2.remove(0);
                    assert(forall | j: int | 0 < j < v1@.len() ==> ghost_fn(e, v1@[0]) && ghost_fn(v1@[0],v1@[j]) ==> #[trigger] ghost_fn(e, v1@[j]));
                    assert(forall | j: int | 0 <= j < v1@.len() ==> ghost_fn(e, v1@[j]));
                    e
                },
            };
            out.push(elem);
            assert(out@.to_multiset().add(v1@.to_multiset()).add(v2@.to_multiset()) =~= g_ms) by {
                out@.to_multiset_ensures();
                v1@.to_multiset_ensures();
                v2@.to_multiset_ensures();
                g_v.to_multiset_ensures();
            };
        }
    }
    proof {
        v1@.to_multiset_ensures();
        v2@.to_multiset_ensures();
    }
    out
}


pub fn merge_sort<T>(mut v: Vec<T>, sort_fn: &impl Fn(&T, &T) -> bool, Ghost(ghost_fn): Ghost<spec_fn(T, T) -> bool>) -> (out: Vec<T>)
    requires
            forall |x: T, y: T| #[trigger] (call_requires(sort_fn, (&x, &y))),
            forall |x: T, y: T, r: bool| #[trigger] call_ensures(sort_fn, (&x, &y), r) ==> r == ghost_fn(x, y),
            total_ordering(ghost_fn),
    ensures
        v@.to_multiset() =~= out@.to_multiset(),
        sorted_by(out@, ghost_fn),
    decreases v.len(),
{
    if v.len() <= 1 {
        return v;
    }
    let mid = v.len() / 2;
    let ghost old_v = v@;
    let v2: Vec<T> = v.split_off(mid);
    let v1 = v;
    proof {
        v1@.to_multiset_ensures();
        v2@.to_multiset_ensures();
    }
    assert(old_v =~= old_v.subrange(0, mid as int).add(old_v.subrange(mid as int, old_v.len() as int)));
    assert(old_v.subrange(0, mid as int) =~= v1@);
    assert(old_v.subrange(mid as int, old_v.len() as int) =~= v2@);
    assert(old_v =~= v1@.add(v2@));
    proof!(vec_add_eq_multiset_add(v1@, v2@));
    let v1_sorted = merge_sort(v1, sort_fn, Ghost(ghost_fn));
    let v2_sorted = merge_sort(v2, sort_fn, Ghost(ghost_fn));
    let retval = merge(v1_sorted, v2_sorted, sort_fn, Ghost(ghost_fn));
    assert(retval@.to_multiset() =~= v1_sorted@.to_multiset().add(v2_sorted@.to_multiset()));
    retval
}

pub fn insertion_sort<T>(mut v: Vec<T>, sort_fn: impl Fn(&T, &T) -> bool, Ghost(ghost_fn): Ghost<spec_fn(T, T) -> bool>) -> (out: Vec<T>)
    requires
            forall |x: T, y: T| #[trigger] (call_requires(sort_fn, (&x, &y))),
            forall |x: T, y: T, r: bool| #[trigger] call_ensures(sort_fn, (&x, &y), r) ==> r == ghost_fn(x, y),
            total_ordering(ghost_fn),
    ensures
        v@.to_multiset() =~= out@.to_multiset(),
        sorted_by(out@, ghost_fn),
{
    if v.len() <= 1 {
        return v;
    }
    let ghost start_vec = v@;
    let ghost s_ms = start_vec.to_multiset();
    let mut index = 0;
    let mut i = 1;
    #[verifier::loop_isolation(false)]
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            0 <= index < v.len(),
            forall |j: int| 0 <= j < i ==> ghost_fn(v[index as int],v[j as int]),
        decreases v.len() - i
    {
        if sort_fn(&v[i], &v[index]) {
            assert(ghost_fn(v[i as int], v[index as int]));
            index = i;
        }
        else {
            assert(!ghost_fn(v[i as int], v[index as int]));
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
    #[verifier::loop_isolation(false)]
    while v.len() > 0
        invariant
            v.len() >= 0,
            out@.len() >= 1,
            forall |i: int| 0 <= i < v@.len() ==> ghost_fn(out@[out@.len() - 1], #[trigger] v@[i]),
            s_ms =~= v@.to_multiset().add(out@.to_multiset()),
            sorted_by(out@, ghost_fn),
        decreases v.len(),
    {
        let mut index = 0;
        let mut i = 1;
        #[verifier::loop_isolation(false)]
        while i < v.len()
            invariant
                1 <= i <= v.len(),
                0 <= index < v.len(),
                forall |j: int| 0 <= j < i ==> ghost_fn(v[index as int],v[j as int]),
            decreases v.len() - i
        {
            if sort_fn(&v[i], &v[index]) {
                assert(ghost_fn(v[i as int], v[index as int]));
                index = i;
            }
            else {
                assert(!ghost_fn(v[i as int], v[index as int]));
            }
            i += 1;
        }
        proof {
            out@.to_multiset_ensures();
            v@.to_multiset_ensures();
        }
        assert(forall |i: int, j: int| 0 <= i < j < out@.len() ==> ghost_fn(out@[i],out@[j]));
        let elem = v.remove(index);
        out.push(elem);
    }
    proof!(v@.to_multiset_ensures());
    out
}

}
