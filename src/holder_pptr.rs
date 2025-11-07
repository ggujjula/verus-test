use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

verus! {

    struct HolderPPtr<V> {
        perm: Option<Tracked<PointsTo<V>>>,
        ptr: Option<PPtr<V>>,
    }

    impl<V> HolderPPtr<V> {
        spec fn wf(&self) -> bool {
            match self.ptr {
                None => self.perm@.is_none(),
                Some(p) => match self.perm {
                    None => false,
                    Some(pt) => pt@.is_init() && pt@.pptr() == p,
                }
            }
        }

        spec fn view(&self) -> Option<V> {
            match self.perm {
                None => None,
                Some(v) => Some(v@.value()),
            }
        }

        fn new() -> (s: Self)
            ensures s.wf()
        {
            Self {
                perm: None,
                ptr: None,
            }
        }

        fn put(&mut self, v: V) -> (res: Result<(), V>)
            requires old(self).wf(),
            ensures self.wf(), match res {
                Ok(()) => self@ == Some(v),
                Err(rv) => rv == v,
            }
        {
            match self.ptr {
                Some(_) => Err(v),
                None => {
                    let (ptr, perm) = PPtr::new(v);
                    self.perm = Some(perm);
                    self.ptr = Some(ptr);
                    Ok(())
                }
            }
        }

        fn pop(&mut self) -> (res: Result<V, ()>)
            requires old(self).wf(),
            ensures self.wf(), match res {
                Ok(rv) => self@ == None::<V>,
                Err(()) => true,
            }
        {
            match self.ptr.take() {
                None => Err(()),
                Some(v) => {
                    assert(self.perm.is_some());
                    Ok(v.into_inner(self.perm.take().unwrap()))
                },
            }
        }
    }

} // verus!
