//use verus_supplemental::seq::lemma_add_ensures;
//use vstd::multiset::Multiset;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::prelude::*;
//use vstd::relations::{
//    antisymmetric, reflexive, sorted_by, strongly_connected, total_ordering, transitive,
//};

verus! {
pub enum ProducerState {
    Idle(nat), // local copy of tail
    Producing(nat),
}

pub enum ConsumerState {
    Idle(nat), // local copy of head
    Consuming(nat),
}

tokenized_state_machine! { SpscQueue<T>{
    fields {
        #[sharding(constant)]
        pub backing_cells: Seq<CellId>,

        #[sharding(storage_map)]
        pub storage: Map<nat, PointsTo<T>>,

        #[sharding(variable)]
        pub head: nat,

        #[sharding(variable)]
        pub tail: nat,

        #[sharding(variable)]
        pub producer: ProducerState,

        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    pub open spec fn len(&self) -> nat {
        self.backing_cells.len()
    }

    pub open spec fn inc_wrap(i: nat, len: nat) -> nat {
        if i + 1 == len { 0 } else { i + 1 }
    }

    #[invariant]
    pub fn in_bounds(&self) -> bool {
        0 <= self.head && self.head < self.backing_cells.len() &&
        0 <= self.tail && self.tail < self.backing_cells.len()
        && match self.producer {
            ProducerState::Producing(tail) => {
                self.tail == tail
            }
            ProducerState::Idle(tail) => {
                self.tail == tail
            }
        }
        && match self.consumer {
            ConsumerState::Consuming(head) => {
                self.head == head
            }
            ConsumerState::Idle(head) => {
                self.head == head
            }
        }
    }

    #[invariant]
    pub fn not_overlapping(&self) -> bool {
        match (self.producer, self.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                head != tail
                && Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                true
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                head != tail
            }
        }
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall|i: nat| 0 <= i && i < self.len() ==>
            self.valid_storage_at_idx(i)
    }

    // Indicates whether we expect a cell to be checked out or not,
    // based on the producer/consumer state.

    pub open spec fn is_checked_out(&self, i: nat) -> bool {
        self.producer === ProducerState::Producing(i)
        || self.consumer === ConsumerState::Consuming(i)
    }

    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            // No cell permission is stored
            !self.storage.dom().contains(i)
        } else {
            // Permission is stored
            self.storage.dom().contains(i)

            // Permission must be for the correct cell:
            && self.storage.index(i).id() === self.backing_cells.index(i as int)

            && if self.in_active_range(i) {
                // The cell is full
                self.storage.index(i).is_init()
            } else {
                // The cell is empty
                self.storage.index(i).is_uninit()
            }
        }
    }

    pub open spec fn in_active_range(&self, i: nat) -> bool {
        // Note that self.head = self.tail means empty range
        0 <= i && i < self.backing_cells.len() && (
            if self.head <= self.tail {
                self.head <= i && i < self.tail
            } else {
                i >= self.head || i < self.tail
            }
        )
    }

    transition! {
        produce_start() {
            require(pre.producer is Idle);

            let tail = pre.producer->Idle_0;
            let head = pre.head;

            assert(0 <= tail < pre.backing_cells.len());

            let next_tail  = Self::inc_wrap(tail, pre.backing_cells.len());

            require(next_tail != head);

            update producer = ProducerState::Producing(tail);

            withdraw storage -= [tail => let perm] by {
                assert(pre.valid_storage_at_idx(tail));
            };

            assert(
                perm.id() === pre.backing_cells.index(tail as int)
                && perm.is_uninit()
            ) by {
                assert(!pre.in_active_range(tail));
                assert(pre.valid_storage_at_idx(tail));
            };
        }
    }

    #[inductive(produce_start)]
    fn produce_start_inductive(pre: Self, post: Self) {
        let tail = pre.producer->Idle_0;
        assert(!pre.in_active_range(tail));
        match (post.producer, post.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(Self::inc_wrap(tail, post.backing_cells.len()) != head);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
                assert(Self::inc_wrap(tail, post.backing_cells.len()) != head);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
            }
        }
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i));
    }

}}
}

use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

struct Queue<T> {
    buffer: Vec<UnsafeCell<MaybeUninit<T>>>,
    head: AtomicU64,
    tail: AtomicU64,
}

pub struct Producer<T> {
    queue: Arc<Queue<T>>,
    tail: usize,
}

pub struct Consumer<T> {
    queue: Arc<Queue<T>>,
    head: usize,
}

pub fn new_queue<T>(len: usize) -> (Producer<T>, Consumer<T>) {
    let mut backing_cells = Vec::new();
    while backing_cells.len() < len {
        let cell = UnsafeCell::new(MaybeUninit::uninit());
        backing_cells.push(cell);
    }

    let head_atomic = AtomicU64::new(0);
    let tail_atomic = AtomicU64::new(0);

    let queue = Queue {
        buffer: backing_cells,
        head: head_atomic,
        tail: tail_atomic,
    };
    let arc = Arc::new(queue);
    let prod = Producer {
        queue: arc.clone(),
        tail: 0,
    };
    let cons = Consumer {
        queue: arc.clone(),
        head: 0,
    };
    (prod, cons)
}

impl<T> Producer<T> {
    fn enqueue(&mut self, t: T) {
        loop {
            let len = self.queue.buffer.len();

            let next_tail = if self.tail + 1 == len {
                0
            } else {
                self.tail + 1
            };

            let head = self.queue.head.load(Ordering::SeqCst);

            if head != next_tail as u64 {
                unsafe {
                    (*self.queue.buffer[self.tail].get()).write(t);
                }

                self.queue.tail.store(next_tail as u64, Ordering::SeqCst);
                self.tail = next_tail;

                return;
            }
        }
    }
}

impl<T> Consumer<T> {
    fn dequeue(&mut self) -> T {
        loop {
            let len = self.queue.buffer.len();

            let next_head = if self.head + 1 == len {
                0
            } else {
                self.head + 1
            };

            let tail = self.queue.tail.load(Ordering::SeqCst);

            if self.head as u64 != tail {
                let t = unsafe {
                    let mut tmp = MaybeUninit::uninit();
                    std::mem::swap(&mut *self.queue.buffer[self.head].get(), &mut tmp);
                    tmp.assume_init()
                };

                self.queue.head.store(next_head as u64, Ordering::SeqCst);
                self.head = next_head;

                return t;
            }
        }
    }
}
