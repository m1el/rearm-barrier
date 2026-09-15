#!/usr/bin/env bash
# Build and audit the theorem entrypoints, rejecting sorryAx and new axioms.
set -euo pipefail
cd "$(dirname "$0")/../model"
lake build RearmBarrier
audit=$(mktemp "${TMPDIR:-/tmp}/rearm-axioms.XXXXXX")
trap 'rm -f "$audit"' EXIT
if ! lake env lean ProofAudit.lean > "$audit" 2>&1; then
  cat "$audit"
  exit 1
fi
cat "$audit"
python3 - "$audit" <<'PY'
import pathlib
import re
import sys

expected = re.findall(r"^#print axioms (\S+)$", pathlib.Path("ProofAudit.lean").read_text(), re.M)
report = pathlib.Path(sys.argv[1]).read_text()
entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", report)
entries += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", report)]
if not expected or sorted(name for name, _ in entries) != sorted(expected):
    sys.exit("FAIL: missing, duplicate, or unexpected axiom reports")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in entries:
    unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - allowed
    if unexpected:
        sys.exit(f"FAIL: {name}: unexpected axioms {sorted(unexpected)}")
print(f"OK: {len(expected)} theorem entrypoints use only approved Lean axioms")
PY
