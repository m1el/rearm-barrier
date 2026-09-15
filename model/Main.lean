import RearmBarrier

open RearmBarrier

def usage : String :=
  "usage:\n" ++
  "  rearm-model storage MAX_WORKERS MAX_CLUSTER   print `w c ticket_storage(w, c)` for every shape\n" ++
  "  rearm-model explore WORKERS CLUSTER COUNT [MAX_STATES]\n" ++
  "                                               exhaustively check every interleaving\n" ++
  "  rearm-model check TRACE_FILE                  check that a crate trace is an execution of the model\n" ++
  "  rearm-model simulate WORKERS CLUSTER COUNT SEED\n" ++
  "                                               print a trace of the model under a random schedule\n"

def fail (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return 1

def nat! (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"expected a number, got `{s}`")

def cmdStorage (maxW maxC : String) : IO UInt32 := do
  let maxW ← nat! maxW
  let maxC ← nat! maxC
  for c in [2:maxC + 1] do
    for w in [1:maxW + 1] do
      IO.println s!"{w} {c} {ticketStorage w c}"
  return 0

def showPath (path : List (Thread × Option Event)) : String :=
  String.join <| path.map fun (t, ev) =>
    match ev with
    | some e => s!"  {t} {e}\n"
    | none => s!"  {t} (local step)\n"

def cmdExplore (w c n : String) (maxStates : Option String) : IO UInt32 := do
  let cfg : Config := { workers := ← nat! w, cluster := ← nat! c, count := ← nat! n }
  if !cfg.valid then
    return ← fail s!"invalid configuration: WORKERS = {cfg.workers}, CLUSTER = {cfg.cluster}"
  let maxStates ← match maxStates with
    | some m => nat! m
    | none => pure 2000000
  let res := explore cfg maxStates
  match res.failure with
  | some (msg, path, s) =>
    IO.println s!"FAIL {cfg.workers} {cfg.cluster} {cfg.count}: {msg}"
    IO.println s!"state:\n{s.describe}"
    IO.println s!"path ({path.length} steps):\n{showPath path}"
    return 1
  | none =>
    if res.truncated then
      IO.println s!"TRUNCATED {cfg.workers} {cfg.cluster} {cfg.count}: more than {maxStates} states; nothing wrong in the {res.states} states visited"
      return 2
    IO.println s!"OK {cfg.workers} {cfg.cluster} {cfg.count}: {res.states} states, {res.transitions} transitions, ticket_storage = {cfg.storage}"
    return 0

def cmdCheck (file : String) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parseTrace text with
  | .error m => fail s!"FAIL {file}: {m}"
  | .ok tr =>
    match replay tr with
    | .error m => fail s!"FAIL {file} (WORKERS = {tr.cfg.workers}, CLUSTER = {tr.cfg.cluster}, count = {tr.cfg.count}):\n{m}"
    | .ok res =>
      IO.println s!"OK {file}: {res.replayed} events, WORKERS = {tr.cfg.workers}, CLUSTER = {tr.cfg.cluster}, count = {tr.cfg.count}, final tickets = {res.final.tickets}"
      return 0

def cmdSimulate (w c n seed : String) : IO UInt32 := do
  let cfg : Config := { workers := ← nat! w, cluster := ← nat! c, count := ← nat! n }
  if !cfg.valid then
    return ← fail s!"invalid configuration: WORKERS = {cfg.workers}, CLUSTER = {cfg.cluster}"
  let seed ← nat! seed
  match simulate cfg seed.toUInt64 with
  | .error m => fail s!"FAIL: {m}"
  | .ok (lines, _) =>
    IO.println s!"config {cfg.workers} {cfg.cluster} {cfg.count}"
    for l in lines do
      IO.println l
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["storage", w, c] => cmdStorage w c
  | ["explore", w, c, n] => cmdExplore w c n none
  | ["explore", w, c, n, m] => cmdExplore w c n (some m)
  | ["check", file] => cmdCheck file
  | ["simulate", w, c, n, seed] => cmdSimulate w c n seed
  | _ => fail usage
