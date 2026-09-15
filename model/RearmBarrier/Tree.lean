/-!
# Ticket tree arithmetic

Mirrors the `const fn`s `ticket_tree_alloc` and `ticket_storage` of
`src/lib.rs`, together with the associated constants `BASE_SIZE`,
`TICKET_TREE_SIZE` and `TICKETS_PER_WORKER`, and proves the sizing claim
that the crate checks at compile time for every instantiation:

    ticket_storage(WORKERS, CLUSTER) <= TICKETS_PER_WORKER * WORKERS

for all `WORKERS >= 1` and `CLUSTER >= 2`.
-/

namespace RearmBarrier

/-- `usize::div_ceil` for a non-zero divisor. -/
def divCeil (n d : Nat) : Nat := (n + d - 1) / d

set_option linter.unusedVariables false in
/-- The loop of `ticket_tree_alloc`. `botSize` is the width of the level
currently being counted and `size` the number of tickets counted so far.

The extra guards `2 ≤ cluster` and `1 ≤ botSize` make the recursion well
founded; under a valid configuration they always hold, so the function agrees
with the Rust loop (which does not terminate for `cluster < 2` and is rejected
at compile time). -/
def ticketTreeAllocAux (baseSize cluster : Nat) (botSize size : Nat) : Nat :=
  if h : botSize * cluster < baseSize ∧ 2 ≤ cluster ∧ 1 ≤ botSize then
    ticketTreeAllocAux baseSize cluster (botSize * cluster) (size + botSize * cluster)
  else
    size
termination_by baseSize - botSize
decreasing_by
  have : botSize * 2 ≤ botSize * cluster := Nat.mul_le_mul_left _ h.2.1
  omega

/-- `ticket_tree_alloc(base_size, cluster)`: the number of tickets strictly
above the lowest level of a tree of fan-in `cluster` whose lowest level has
`base_size` tickets. -/
def ticketTreeAlloc (baseSize cluster : Nat) : Nat :=
  ticketTreeAllocAux baseSize cluster 1 1

/-- `ticket_storage(workers, cluster)`: the total number of tickets. -/
def ticketStorage (workers cluster : Nat) : Nat :=
  ticketTreeAlloc (divCeil workers cluster) cluster + divCeil workers cluster

/-- `RearmBarrier::BASE_SIZE` -/
def baseSize (workers cluster : Nat) : Nat := divCeil workers cluster

/-- `RearmBarrier::TICKET_TREE_SIZE` -/
def ticketTreeSize (workers cluster : Nat) : Nat :=
  ticketTreeAlloc (baseSize workers cluster) cluster

/-- `TICKETS_PER_WORKER` -/
def ticketsPerWorker : Nat := 2

/-- The parent of heap node `i` (`(ticket_id - 1) / CLUSTER`). -/
def parent (i cluster : Nat) : Nat := (i - 1) / cluster

/-- The examples from the crate's `ticket_storage_examples` test. -/
theorem ticketStorage_examples :
    ticketStorage 5 2 = 6 ∧ ticketStorage 7 2 = 7 ∧
    ticketStorage 1 2 = 2 ∧ ticketStorage 9 3 = 4 := by
  native_decide

/-- Loop invariant: the tickets added above the lowest level are bounded by
twice the width of the widest level counted, which is below `baseSize`. -/
theorem ticketTreeAllocAux_le (baseSize cluster : Nat) (hc : 2 ≤ cluster) :
    ∀ botSize size,
      ticketTreeAllocAux baseSize cluster botSize size ≤
        size + (2 * baseSize - 2 - 2 * botSize) := by
  intro botSize size
  induction botSize, size using ticketTreeAllocAux.induct baseSize cluster with
  | case1 botSize size h ih =>
    unfold ticketTreeAllocAux
    simp only [h, and_self, ↓reduceDIte]
    have : botSize * 2 ≤ botSize * cluster := Nat.mul_le_mul_left _ hc
    omega
  | case2 botSize size h =>
    unfold ticketTreeAllocAux
    simp only [h, ↓reduceDIte]
    omega

theorem ticketTreeAlloc_le (b c : Nat) (hc : 2 ≤ c) :
    ticketTreeAlloc b c ≤ 1 + (2 * b - 4) := by
  unfold ticketTreeAlloc
  have := ticketTreeAllocAux_le b c hc 1 1
  omega

/-- `ceil(w / c) ≤ ceil(w / 2)` for `c ≥ 2`, in multiplied-out form. -/
theorem two_mul_divCeil_le (w c : Nat) (hc : 2 ≤ c) : 2 * divCeil w c ≤ w + 1 := by
  unfold divCeil
  have h1 : (w + c - 1) / c * c ≤ w + c - 1 := Nat.div_mul_le_self _ _
  generalize (w + c - 1) / c = q at h1
  cases q with
  | zero => omega
  | succ q' =>
    have h2 : q' * 2 ≤ q' * c := Nat.mul_le_mul_left _ hc
    rw [Nat.succ_mul] at h1
    omega

/-- The compile-time assertion in `RearmBarrier::new`, for every valid
configuration. -/
theorem ticketStorage_le (w c : Nat) (_hw : 1 ≤ w) (hc : 2 ≤ c) :
    ticketStorage w c ≤ ticketsPerWorker * w := by
  unfold ticketStorage ticketsPerWorker
  have h1 := ticketTreeAlloc_le (divCeil w c) c hc
  have h2 := two_mul_divCeil_le w c hc
  omega

/-- Walking up the heap strictly decreases the index, so the ticket walk in
`consumer` terminates. -/
theorem parent_lt (i c : Nat) (hi : 1 ≤ i) : parent i c < i := by
  unfold parent
  have := Nat.div_le_self (i - 1) c
  omega

/-- The first ticket a consumer touches, `TICKET_TREE_SIZE + id / CLUSTER`,
lies inside the `ticket_storage` prefix of the array. Every later ticket is a
parent and hence smaller, so the whole walk stays in bounds. -/
theorem start_ticket_lt (w c id : Nat) (hc : 1 ≤ c) (hid : id < w) :
    ticketTreeSize w c + id / c < ticketStorage w c := by
  unfold ticketTreeSize ticketStorage baseSize divCeil
  have h1 : id / c ≤ (w - 1) / c := Nat.div_le_div_right (by omega)
  have h3 : w + c - 1 = w - 1 + c := by omega
  rw [h3]
  cases c with
  | zero => omega
  | succ c' =>
    have h2 : (w - 1 + (c' + 1)) / (c' + 1) = (w - 1) / (c' + 1) + 1 :=
      Nat.add_div_right _ (by omega)
    rw [h2]
    omega

end RearmBarrier
