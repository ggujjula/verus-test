use std::sync::Arc;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::cell::CellId;
use vstd::cell::PCell;
use vstd::cell::PointsTo;
use vstd::map::Map;
use vstd::prelude::*;
use vstd::thread::*;

verus! {

tokenized_state_machine!{
    SCQ<T> {
        fields {
            #[sharding(constant)]
            pub n: nat,

            #[sharding(constant)]
            pub data_ids: Seq<CellId>,

            #[sharding(storage_map)]
            pub data: Map<nat, PointsTo<T>>,

            #[sharding(constant)]
            pub aq: Seq<CellId>,

            #[sharding(storage_map)]
            pub aq_storage: Map<nat, PointsTo<usize>>,

            #[sharding(constant)]
            pub fq: Seq<CellId>,

            #[sharding(storage_map)]
            pub fq_storage: Map<nat, PointsTo<usize>>,

            #[sharding(variable)]
            pub aq_head: nat,
            #[sharding(variable)]
            pub aq_tail: nat,

            #[sharding(variable)]
            pub fq_head: nat,
            #[sharding(variable)]
            pub fq_tail: nat,
        }

        pub open spec fn len(&self) -> nat {
            self.n
        }

        pub open spec fn cycle(&self, counter: nat) -> nat {
            counter / self.len()
        }

        pub open spec fn offset(&self, counter: nat) -> nat {
            counter % self.len()
        }

        #[invariant]
        pub fn in_bounds(&self) -> bool {
            self.aq_head <= self.aq_tail &&
            self.fq_head <= self.fq_tail
        }

        init!{
            initialize(backing_cells: Seq<CellId>, storage: Map<nat, PointsTo<T>>,
                        aq: Seq<CellId>, aq_storage: Map<nat, PointsTo<usize>>,
                        fq: Seq<CellId>, fq_storage: Map<nat, PointsTo<usize>>)
            {
                // Upon initialization, the user needs to deposit _all_ the relevant
                // cell permissions to start with. Each permission should indicate
                // an empty cell.
                require(backing_cells.len() == aq.len() == fq.len());
                let n = backing_cells.len();
                require(n > 0);

                require(
                    (forall|i: nat| 0 <= i && i < backing_cells.len() ==>
                        #[trigger] storage.dom().contains(i)
                        && storage.index(i).id() === backing_cells.index(i as int)
                        && storage.index(i).is_uninit())
                );
                require(
                    (forall|i: nat| 0 <= i && i < aq.len() ==>
                        #[trigger] aq_storage.dom().contains(i)
                        && aq_storage.index(i).id() === aq.index(i as int)
                        && aq_storage.index(i).is_uninit())
                );
                require(
                    (forall|i: nat| 0 <= i && i < fq.len() ==>
                        #[trigger] fq_storage.dom().contains(i)
                        && fq_storage.index(i).id() === fq.index(i as int)
                        && fq_storage.index(i).is_uninit())
                );

                init n = backing_cells.len();
                init data_ids = backing_cells;
                init data = storage;
                init aq = aq;
                init aq_storage = aq_storage;
                init fq = fq;
                init fq_storage = fq_storage;
                init aq_head = 0;
                init aq_tail = 0;
                init fq_head = 0;
                init fq_tail = 0;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post:Self, backing_cells: Seq<CellId>, storage: Map<nat, PointsTo<T>>,
                        aq: Seq<CellId>, aq_storage: Map<nat, PointsTo<usize>>,
                        fq: Seq<CellId>, fq_storage: Map<nat, PointsTo<usize>>)
        {

        }
    }
}

struct Queue<T> {
    n: usize,
    data: Vec<PCell<T>>,
    aq: Vec<PCell<usize>>,
    fq: Vec<PCell<usize>>,
    instance: Tracked<SCQ::Instance<T>>,
    aq_head: AtomicUsize<Tracked<SCQ::Instance<T>>, SCQ::aq_head<T>, AlwaysGoodPred>,
    aq_tail: AtomicUsize<Tracked<SCQ::Instance<T>>, SCQ::aq_tail<T>, AlwaysGoodPred>,
    fq_head: AtomicUsize<Tracked<SCQ::Instance<T>>, SCQ::fq_head<T>, AlwaysGoodPred>,
    fq_tail: AtomicUsize<Tracked<SCQ::Instance<T>>, SCQ::fq_tail<T>, AlwaysGoodPred>,

}

pub struct Worker<T> {
    queue: Arc<Queue<T>>,
}

exec fn populate_pcell_vec<T>(n: usize) -> (out: (Vec<PCell<T>>, Tracked<Map<nat, PointsTo<T>>>))
    requires
        n > 0,
    ensures
        forall |j: nat|
        #![trigger( out.1@.dom().contains(j) )]
        #![trigger( out.0@.index(j as int) )]
        #![trigger( out.1@.index(j) )]
        0 <= j < out.0.len() ==> out.1@.dom().contains(j)
        && out.0@.index(j as int).id() === out.1@.index(j).id()
        && out.1@.index(j).is_uninit(),
        out.0@.len() == n,
{
    let mut data = Vec::<PCell<T>>::new();
    let tracked mut data_perms = Map::<nat, PointsTo<T>>::tracked_empty();

    while data.len() < n
        invariant
            forall |j: nat|
            #![trigger( data_perms.dom().contains(j) )]
            #![trigger( data@.index(j as int) )]
            #![trigger( data_perms.index(j) )]
            0 <= j < data.len() ==> data_perms.dom().contains(j)
            && data@.index(j as int).id() === data_perms.index(j).id()
            && data_perms.index(j).is_uninit(),
            data.len() <= n,
        decreases
            n - data.len(),
    {
        let ghost i = data.len();
        let (cell, cell_perm) = PCell::empty();
        data.push(cell);
        proof {
            data_perms.tracked_insert(i as nat, cell_perm.get());
        }
    }

    (data, Tracked(data_perms))
}

struct AlwaysGoodPred;

impl<K, V, G> AtomicInvariantPredicate<K, V, G> for AlwaysGoodPred {
    open spec fn atomic_inv(k: K, v: V, g: G) -> bool {
        true
    }
}

pub fn new<T>(n: usize) -> Worker<T>
    requires
        n > 0,
//    ensures,
{
    let (data, Tracked(data_perms)) = populate_pcell_vec::<T>(n);
    let (aq, Tracked(aq_perms)) = populate_pcell_vec::<usize>(n);
    let (fq, Tracked(fq_perms)) = populate_pcell_vec::<usize>(n);

    let ghost mut data_ids = Seq::<CellId>::new(
    data@.len(),
    |i: int| data@.index(i).id(),
    );
    let ghost mut aq_ids = Seq::<CellId>::new(
    aq@.len(),
    |i: int| aq@.index(i).id(),
    );
    let ghost mut fq_ids = Seq::<CellId>::new(
    fq@.len(),
    |i: int| fq@.index(i).id(),
    );

    let tracked (
        Tracked(instance),
        Tracked(aq_head),
        Tracked(aq_tail),
        Tracked(fq_head),
        Tracked(fq_tail),
    ) = SCQ::Instance::initialize(data_ids, data_perms, aq_ids, aq_perms, fq_ids, fq_perms, data_perms, aq_perms, fq_perms);

    let tracked_inst = Tracked(instance.clone());
    let aq_head = AtomicUsize::<_, _, AlwaysGoodPred>::new(Ghost(tracked_inst), 0, Tracked(aq_head));
    let aq_tail = AtomicUsize::<_, _, AlwaysGoodPred>::new(Ghost(tracked_inst), 0, Tracked(aq_tail));
    let fq_head = AtomicUsize::<_, _, AlwaysGoodPred>::new(Ghost(tracked_inst), 0, Tracked(fq_head));
    let fq_tail = AtomicUsize::<_, _, AlwaysGoodPred>::new(Ghost(tracked_inst), 0, Tracked(fq_tail));

    let queue = Queue {
        n,
        data,
        aq,
        fq,
        aq_head,
        aq_tail,
        fq_head,
        fq_tail,
        instance: Tracked(instance),
    };
    Worker {
        queue: Arc::new(queue),
    }
}



} // verus!
