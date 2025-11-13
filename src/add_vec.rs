use vstd::prelude::*;

verus! {

spec fn cast_vec_to_seq(v: &Vec<u64>) -> Seq<int> {
    v@.map(|_index:int, i:u64| i as int)
}

spec fn add_vec_spec(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[v.len() - 1] + add_vec_spec(v.subrange(0, v.len() - 1))
    }
}

proof fn suffix_is_subset<A>(p: Seq<A>, s: Seq<A>)
    requires p.is_suffix_of(s),
    ensures p.to_multiset().subset_of(s.to_multiset()),
{
    let pr = p.reverse();
    let sr = s.reverse();
    prefix_is_subset(pr, sr);
    assert(pr.to_multiset() =~= p.to_multiset()) by { p.lemma_reverse_to_multiset() };
    assert(sr.to_multiset() =~= s.to_multiset()) by { s.lemma_reverse_to_multiset() };
}

proof fn prefix_is_subset<A>(p: Seq<A>, s: Seq<A>)
    requires p.is_prefix_of(s),
    ensures p.to_multiset().subset_of(s.to_multiset()),
    decreases p.len(), s.len()
{
    let p_ms = p.to_multiset();
    let s_ms = s.to_multiset();
    p.to_multiset_ensures();
    s.to_multiset_ensures();
    if p.len() > 0 {
        let elem = s.last();
        let s_small = s.drop_last();
        let ss_ms = s_small.to_multiset();
        s_small.to_multiset_ensures();
        assert(s_small.push(elem) =~= s);
        if p.len() == s.len() {
            let p_small = p.drop_last();
            let ps_ms = p_small.to_multiset();
            p_small.to_multiset_ensures();
            prefix_is_subset(p_small, s_small);
            assert(p_small.push(elem) =~= p);
        } else {
            prefix_is_subset(p, s_small);
        }
    }
}

fn add_vec(v: &Vec<u64>) -> (ret: Option<u64>)
    ensures (
        match ret {
            None => {
                exists |subset: Seq<int>| (
                    subset.to_multiset().subset_of(cast_vec_to_seq(v).to_multiset()) &&
                    #[trigger] add_vec_spec(subset) > u64::MAX
                )
            }
            Some(sum) => {
                sum == add_vec_spec(cast_vec_to_seq(v))
            }
        }
    )
{
    let mut sum: u64 = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum == add_vec_spec(cast_vec_to_seq(v).subrange(0, i as int)),
        decreases
            v.len() - i
    {
        proof {
            let small = cast_vec_to_seq(v).subrange(0, i as int);
            let big = cast_vec_to_seq(v).subrange(0, (i as int) + 1);
            assert(big.drop_last() =~= small);
        }
        match sum.checked_add(v[i]) {
            Some(new_sum) => {
                sum = new_sum;
            }
            None => {
                proof {
                    let s = cast_vec_to_seq(v);
                    let p = s.subrange(0, (i as int) + 1);
                    assert(sum + v[i as int] == add_vec_spec(p));
                    prefix_is_subset(p, s);
                }
                return None;
            }
        }
        i += 1;
    }
    assert(cast_vec_to_seq(v) =~= cast_vec_to_seq(v).subrange(0, v.len() as int));
    Some(sum)
}

}
