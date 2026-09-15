# rearm-barrier

A re-arming broadcast barrier for low-latency benchmarking of tasks across a
fixed set of worker threads. `no_std`, allocation-free, stable Rust.

One producer builds a job, it is broadcast to `WORKERS` consumers behind a
shared reference, every consumer processes it and writes into its own
cache-line-aligned result slot, the producer observes all results, and the
barrier re-arms for the next job. All waiting is by spinning.

Completion is tracked through a tree of counters with fan-in `CLUSTER`, so
finishing workers touch different cache lines instead of one hot counter.

```rust
use rearm_barrier::RearmBarrier;

const WORKERS: usize = 4;
let barrier = RearmBarrier::<u64, u64, WORKERS, 2>::new();

std::thread::scope(|s| {
    for id in 0..WORKERS {
        let barrier = &barrier;
        s.spawn(move || {
            barrier.consumer(100, id, 0, |_version, job, result| {
                *result = job * id as u64;
            });
        });
    }

    barrier.producer(100, |version| version as u64 + 1, |version, results| {
        for (id, r) in results.iter().enumerate() {
            assert_eq!(**r, (version as u64 + 1) * id as u64);
        }
    });
});
```

`RearmBarrier::new` is a `const fn`, so a barrier can live in a `static`.
Invalid configurations (`WORKERS == 0`, `CLUSTER < 2`) are rejected at
compile time.

## Testing

```
cargo test --release
```
