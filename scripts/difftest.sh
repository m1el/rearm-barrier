#!/usr/bin/env bash
# Differential test of the crate against the Lean model in model/.
#
#   1. ticket_storage: the crate's const fn and the model's ticketStorage must
#      agree on every shape up to 4096 workers and fan-in 16.
#   2. The model alone: exhaustive exploration of every interleaving of small
#      shapes must find no invariant violation and no deadlock.
#   3. Traces: the instrumented crate (feature `trace`) runs real threads and
#      records every atomic operation; `rearm-model check` must accept each
#      trace as an execution of the model that satisfies every invariant.
#
# Environment: ITERS (traces per shape, default 10), COUNT (max versions per
# trace, default 64), MAX_WORKERS (skip shapes with more workers; default
# cores - 1, since oversubscribed spinning threads are slow), TIMEOUT (seconds
# after which a run counts as hung and its partial trace is checked, default
# 120), OUT (directory for failing traces, default target/difftest).
set -euo pipefail
cd "$(dirname "$0")/.."

ITERS=${ITERS:-10}
COUNT=${COUNT:-64}
TIMEOUT=${TIMEOUT:-120}
OUT=${OUT:-target/difftest}
cores=$( (sysctl -n hw.ncpu || nproc) 2>/dev/null || echo 4)
MAX_WORKERS=${MAX_WORKERS:-$((cores - 1))}

cargo build --release --features trace --example trace
(cd model && lake build)
MODEL=model/.lake/build/bin/rearm-model
HARNESS=target/release/examples/trace
mkdir -p "$OUT"

echo "== ticket_storage: crate vs model"
"$HARNESS" storage 4096 16 > "$OUT/storage.crate"
"$MODEL" storage 4096 16 > "$OUT/storage.model"
diff "$OUT/storage.crate" "$OUT/storage.model"
echo "ok: $(wc -l < "$OUT/storage.model" | tr -d ' ') shapes agree"

echo "== model: exhaustive exploration of small shapes"
for shape in "1 2 3" "2 2 3" "3 2 3" "4 2 2" "5 2 2" "3 3 2" "4 3 2" "5 3 1" "4 4 2" "6 8 1"; do
  # shellcheck disable=SC2086
  "$MODEL" explore $shape
done

echo "== traces: crate executions replayed on the model (max $MAX_WORKERS workers, $ITERS per shape)"
fails=0
n=0
while read -r w c; do
  (( w <= MAX_WORKERS )) || continue
  for seed in $(seq 1 "$ITERS"); do
    count=$(( (seed * 7919 + w * 31 + c) % COUNT + 1 ))
    level=$(( seed % 3 ))
    f="$OUT/trace-w${w}-c${c}-n${count}-s${seed}.txt"
    "$HARNESS" run "$w" "$c" "$count" "$seed" "$level" "$TIMEOUT" > "$f" || true
    if "$MODEL" check "$f" > "$f.log" 2>&1; then
      rm -f "$f" "$f.log"
    else
      fails=$((fails + 1))
      cat "$f.log"
      echo "trace kept at $f"
    fi
    n=$((n + 1))
  done
done < <("$HARNESS" shapes)
echo "$n traces checked, $fails failures"
[ "$fails" -eq 0 ]
