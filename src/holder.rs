use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

verus! {

    struct Holder<V> {
        empty: bool,
        val: Option<V>,
    }

    impl<V> Holder<V> {
        spec fn wf(&self) -> bool {
            match self.empty {
                true => self.val.is_none(),
                false => self.val.is_some(),
            }
        }

        spec fn view(&self) -> Option<V> {
            self.val
        }

        fn new() -> (s: Self)
            ensures s.wf()
        {
            Self {
                empty: true,
                val: None,
            }
        }

        fn put(&mut self, v: V) -> (res: Result<(), V>)
            requires old(self).wf(),
            ensures self.wf(), match res {
                Ok(()) => self@ == Some(v),
                Err(rv) => rv == v,
            }
        {
            match self.val {
                Some(_) => Err(v),
                None => {
                    self.val = Some(v);
                    self.empty = false;
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
            match self.val.take() {
                Some(v) => {
                    self.empty = true;
                    Ok(v)
                },
                None => {
                    Err(())
                }
            }
        }
    }

} // verus!
