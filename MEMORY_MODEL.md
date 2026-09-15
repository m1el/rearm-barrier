# Memory-model proof boundary

The Lean safety results apply to two precisely defined operational models.
A separate graph theorem constructs a compatible ordering of happens-before
and one coherent modification order. None of these results infer SC from race
freedom. The full event/state and clock correspondence from Rust atomic
executions into the operational models remains to be formalized.

Rust documents its atomics in terms of the C++20 rules, with Rust-specific
adjustments. This is the intended external semantics, not an additional Lean
axiom. [Rust atomic memory model](https://doc.rust-lang.org/std/sync/atomic/)

## What is now proved

`model/RearmBarrier/WeakMemory.lean` defines a history machine independently
of the protocol invariant. Its transition rules allow:

- Every probe write to remain available to later loads, including the initial
  zero. A history entry contains its value and its release clock.
- A relaxed load to choose any recorded entry. There is no latest-value
  requirement, coherence restriction, or eventual-visibility assumption.
- An unsuccessful load to repeat arbitrarily, without acquiring anything.
- A successful load to save the selected entry, without acquiring yet.
- Other threads to execute while that load's thread is paused before its fence.
- The fence to use the saved entry's clock, not a newly sampled clock.

The waiting thread cannot perform another action before its pending fence;
this is program order. RMWs and non-atomic access abstractions retain the
original executable model's semantics. In particular, RMWs are still globally
interleaved; this extension is not a general axiomatic weak-memory model.

The following are kernel-checked results, with no new axioms:

| Theorem | Conclusion |
| --- | --- |
| `consumer_probe_bound` | A consumer waiting for `v` implies `probe ≤ 2*v+1`. |
| `consumer_observed_eq` | A recorded value passing that consumer's guard is exactly `2*v+1` and equals the current probe. |
| `producer_observed_eq` | A recorded value passing the producer's completion guard equals the current probe. |
| `Waiting.probe_stable`, `step_probeRel` | Other threads cannot change the signal or its release clock before the recipient's fence. |
| `consumer_reads_publication` | A successful consumer load identifies an actual publication RMW of its version. |
| `producer_reads_completion` | A completion observation identifies an actual consumer finish RMW of that version. |
| `pending_write_stable` | The saved value/clock pair is still current at every reachable pending-fence state. |
| `transition_projects`, `reachable_projection` | Every history-machine action is a stutter or an original step; every reachable history state projects to an original reachable state. |
| `lift_step`, `lift_reachable` | Every original execution can also execute in the history machine, using a separate load and fence for each wait exit. |
| `reachable_attempt_no_race`, `reachable_attempt_no_fault` | No next non-load action races under `Strong`, or faults for a valid thread. Loads only read atomic history and save observations. |
| `reachable_violations_nil`, `reachable_finalViolations_nil` | The original specification checks hold in the history machine too. |

All names in this table are in `RearmBarrier.WeakMemory`.

### Why the signal is stable

A consumer cannot contribute to completing version `v` until after its wait
and callback. While it is waiting, the tree cannot complete that version. A
producer cannot publish version `v+1` until after its wait and completion
callback for `v`. Thus a successful consumer read sees `2*v+1`, and a successful
producer read sees `2*v+2`. The same obstruction holds while either thread is
paused between its load and fence. This establishes equality of the saved and
current clocks, rather than giving the fence extra synchronization by reading
a newer clock.

### Why this induction is not circular

`MachineInv` contains original-model reachability, history consistency, and
pending-fence consistency. `machine_init` proves it initially.
`transition_inv` proves all three together across each history-machine action:

1. A failed load changes nothing.
2. A successful load uses the invariant of the already related original
   state to prove that the selected old write must be the current signal.
3. An ordinary action is an original step; any other thread's pending signal
   remains stable.
4. At a fence, the saved pair equals the current pair. Therefore the fence
   really is an original step, and original reachability extends by that step.

There is no constructor requiring a new history-machine state to satisfy
`Inv`, or requiring its load to read the latest entry. Those are conclusions.
`lift_reachable` additionally rules out obtaining safety merely by excluding
original executions.

This induction does **not** establish original-model reachability for arbitrary
C++ execution graphs. Applying it to such graphs before constructing their
history-machine executions would still be circular.

## How the clock transfers correspond to synchronization

The model uses the following standard rules:

- An RMW reads the immediately preceding modification of its location in
  modification order. An acquire operation reading a release or its release
  sequence synchronizes with that release.
  [Atomic ordering rules](https://eel.is/c++draft/atomics.order)
- A sequence consisting entirely of RMWs continues the release sequence. This
  explains retaining earlier releases in a location's cumulative clock.
  [Release sequences](https://eel.is/c++draft/intro.races)
- A relaxed read can supply synchronization to a following acquire fence
  through the release write it observed (or that write's release sequence).
  It is the observed write that matters, not the location's value at fence time.
  [Fence rules](https://eel.is/c++draft/atomics.fences),
  [Rust fences](https://doc.rust-lang.org/std/sync/atomic/fn.fence.html)

For the crate's `Strong` orderings, these give the intended interpretation of
`Hb.lean`'s clock transfers:

| Concrete edge | Existing invariant clause |
| --- | --- |
| Job write and previous result completion precede publication; consumer acquires through publication. | `published`, `beforeFunc` |
| Consumer result access precedes its release into its leaf ticket. | `TreeHb.leaf` |
| A completing walker acquires previous releases on that ticket and releases them into its parent. | `TreeHb.walker`, `TreeHb.counted`, `TreeHb.filled` |
| The final walker releases accumulated results onto the probe. | `finisherKnows`, `probeKnows` |
| Producer reads that finish write and acquires through its fence before accessing results. | `producerKnows` |

The new provenance and fence-stability theorems supply the missing *operational*
read-from identification at the probe. This table is a correspondence argument,
not a new Lean theorem translating vector clocks into an external C++ execution
graph. That translation is part of the next obligation below.

## Finite execution ordering: proved independently

`model/RearmBarrier/ExecutionOrder.lean` proves the part that cannot follow
from a generic appeal to DRF-SC. `Graph` assumes only a transitive, irreflexive
happens-before relation, a transitive, irreflexive probe modification order,
and write-write coherence: HB between two probe writes implies their probe
modification order. It does not assume that their union is acyclic, that a
global schedule exists, that the program is race-free, or that `Inv` holds.

- `Path.compress` compresses any path in the union into either HB alone or
  HB / one probe-order segment / HB.
- `acyclic` rules out a cycle: a cycle using a probe-order segment would give
  HB (or equality) back from its end to its beginning. Coherence then gives
  the reverse probe order, contradicting irreflexivity.
- For finite events `Fin n`, `rank` counts strict predecessors in the union's
  transitive closure. It strictly increases along every edge.
- `key g e = rank g e * (n+1) + e.val` breaks rank ties. `key_before` proves
  that HB and probe-order edges increase the key; `key_injective` proves
  distinct events have distinct keys. Sorting by this key therefore provides
  a compatible ordering. No global ordering is supplied as a hypothesis.

Why **one** extra location is sufficient for the barrier's `Strong` orderings:
all ticket RMWs acquire and release, so their modification-order edges are
already HB edges through release sequences. Every probe RMW releases. A
successful probe load's release source is HB-before its acquire fence. Keep
that source-to-fence edge and place the abstract successful read at its fence;
the source will already be available in history. The only remaining non-HB
modification-order edges belong to the probe. The generic graph theorem applies
once these semantic facts are instantiated. This interpretation uses the
standard ordering and fence rules linked above; the instantiation from a fully
labeled Rust/C++ graph is not yet a Lean theorem.

This explains why adding arbitrary locations' modification orders to HB is
not the right proof strategy. Coherence only compares writes to the same
location; `Path.compress` needs the endpoints of each intervening HB segment
to be writes to the single distinguished probe.

## Remaining external correspondence obligation

The required direction is **Rust executions into the history machine**.
Constructing a Rust-like graph from a model run proves the opposite direction
and is insufficient for safety coverage.

A future `ExecutionGraph` development should make program order, per-location
modification order, read-from edges, and synchronizes-with explicit. Its target
is: every relevant finite execution of the barrier's atomic control protocol
admits a history-machine execution preserving its non-atomic access order and
all happens-before edges used to establish their safety. This must cover
candidate conflicting accesses, rather than assuming the source is already
race-free. In particular it must establish:

1. **Instantiate the proved ordering theorem.** Translate the source's HB
   and probe modification order to `ExecutionOrder.Graph`. Establish that
   ticket order and publication/finish-to-fence edges are HB under `Strong`.
   Apply `key_before` and `key_injective`; no SC premise is required.
2. **Reconstruct program states in that order.** Place a successful load
   immediately before its fence. Its supplying write is earlier by HB;
   per-thread order fixes its phase, and modification order fixes RMW return
   values. Inductively show the source instructions match history-machine
   actions. Only then use `reachable_machineInv` for the constructed prefix.
   The history model permits stale/incoherent past choices, but does not
   represent reads from writes absent from its execution prefix.
3. **Clock soundness.** Every positive epoch relied on by a model clock must
   correspond to a real sequenced-before/synchronizes-with path. Extra language
   synchronization may be omitted for a safety overapproximation; invented
   synchronization may not. Failed spin reads can contribute to a later fence
   in the language even though this model only uses the successful read.
4. **Access abstraction.** Relate the model's begin/end callback accesses and
   initialization to the real accesses and reference lifetimes, including the
   zero-clock initialization convention. The model must not hide a conflicting
   access by grouping it into a callback step.

These obligations are not hypotheses hidden in `reachable_projection`.
`ExecutionOrder.Graph` describes relations, not the source program's labeled
instructions or access events. There is still no end-to-end external coverage
theorem. The history reduction and compatible-order construction close two
specific proof obligations without claiming a completed Rust memory-model proof.

The machine uses `Nat` and a single common `count`. Relating it to Rust also
requires no-overflow bounds for counters and arithmetic, the attached-thread
and callback assumptions, and treatment of destruction/unwinding if claiming
safety of the whole public API. Safety reduction does not imply eventual
visibility, fair scheduling, callback termination, or deadlock freedom.

## Validation

From the repository root:

```sh
(cd model && lake build)
./scripts/check_axioms.sh
./scripts/difftest.sh
```

`check_axioms.sh` checks the named safety, reduction, provenance, and converse
results for any axioms other than `propext`, `Classical.choice`, and `Quot.sound`.
The number of replayed traces depends on `MAX_WORKERS` and `ITERS`; it is not
always 140. The explorer still runs the original finite model. The history
extension is verified by its theorems, not by enumerating unbounded histories.
