import RearmBarrier

open RearmBarrier

def usage : String :=
  "usage: rearm-model [flat|tree|both] COMMAND ...\n" ++
  "  the engine selects the ticket representation: the crate's flat heap array, the\n" ++
  "  structural tree, or both in lockstep (the default), which faults if they disagree\n\n" ++
  "  storage MAX_WORKERS MAX_CLUSTER       print `w c ticket_storage(w, c)` for every shape\n" ++
  "  explore WORKERS CLUSTER COUNT [MAX_STATES] [WEAKEN...]\n" ++
  "                                       exhaustively check every interleaving; WEAKEN is any of\n" ++
  "                                       publish, ticket, finish (fetch_add -> Relaxed),\n" ++
  "                                       producer-fence, consumer-fence (drop the Acquire fence)\n" ++
  "  check TRACE_FILE                      check that a crate trace is an execution of the model\n" ++
  "  simulate WORKERS CLUSTER COUNT SEED   print a trace of the model under a random schedule\n"

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

def weaken (o : Orderings) : String → Option Orderings
  | "publish" => some { o with publish := .relaxed }
  | "ticket" => some { o with ticket := .relaxed }
  | "finish" => some { o with finish := .relaxed }
  | "producer-fence" => some { o with producerFence := false }
  | "consumer-fence" => some { o with consumerFence := false }
  | _ => none

section

variable {τ κ : Type} [BEq τ] [Hashable τ] [Inhabited τ] [BEq κ] [Hashable κ] [Inhabited κ] [ToString κ]

def cmdExplore (E : Engine τ κ) (w c n : String) (rest : List String) : IO UInt32 := do
  let mut cfg : Config := { workers := ← nat! w, cluster := ← nat! c, count := ← nat! n }
  if !cfg.valid then
    return ← fail s!"invalid configuration: WORKERS = {cfg.workers}, CLUSTER = {cfg.cluster}"
  let mut maxStates := 2000000
  let mut weakened : List String := []
  for arg in rest do
    match arg.toNat? with
    | some m => maxStates := m
    | none =>
      match weaken cfg.orderings arg with
      | some o =>
        cfg := { cfg with orderings := o }
        weakened := weakened ++ [arg]
      | none => return ← fail s!"unknown argument `{arg}`\n{usage}"
  if !weakened.isEmpty then
    IO.println s!"weakened orderings: {weakened}"
  let res := explore E cfg maxStates
  match res.failure with
  | some (msg, path, s) =>
    IO.println s!"FAIL {cfg.workers} {cfg.cluster} {cfg.count}: {msg}"
    IO.println s!"state:\n{s.describe E}"
    IO.println s!"path ({path.length} steps):\n{showPath path}"
    return 1
  | none =>
    if res.truncated then
      IO.println s!"TRUNCATED {cfg.workers} {cfg.cluster} {cfg.count}: more than {maxStates} states; nothing wrong in the {res.states} states visited"
      return 2
    IO.println s!"OK {cfg.workers} {cfg.cluster} {cfg.count}: {res.states} states, {res.transitions} transitions, ticket_storage = {cfg.storage}"
    return 0

def cmdCheck (E : Engine τ κ) (file : String) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parseTrace text with
  | .error m => fail s!"FAIL {file}: {m}"
  | .ok tr =>
    match replay E tr with
    | .error m => fail s!"FAIL {file} (WORKERS = {tr.cfg.workers}, CLUSTER = {tr.cfg.cluster}, count = {tr.cfg.count}):\n{m}"
    | .ok res =>
      IO.println s!"OK {file}: {res.replayed} events, WORKERS = {tr.cfg.workers}, CLUSTER = {tr.cfg.cluster}, count = {tr.cfg.count}, final {E.summary res.final.tickets}"
      return 0

def cmdSimulate (E : Engine τ κ) (w c n seed : String) : IO UInt32 := do
  let cfg : Config := { workers := ← nat! w, cluster := ← nat! c, count := ← nat! n }
  if !cfg.valid then
    return ← fail s!"invalid configuration: WORKERS = {cfg.workers}, CLUSTER = {cfg.cluster}"
  let seed ← nat! seed
  match simulate E cfg seed.toUInt64 with
  | .error m => fail s!"FAIL: {m}"
  | .ok (lines, _) =>
    IO.println s!"config {cfg.workers} {cfg.cluster} {cfg.count}"
    for l in lines do
      IO.println l
    return 0

def dispatch (E : Engine τ κ) (args : List String) : IO UInt32 :=
  match args with
  | ["storage", w, c] => cmdStorage w c
  | "explore" :: w :: c :: n :: rest => cmdExplore E w c n rest
  | ["check", file] => cmdCheck E file
  | ["simulate", w, c, n, seed] => cmdSimulate E w c n seed
  | _ => fail usage

end

def main (args : List String) : IO UInt32 := do
  match args with
  | "flat" :: rest => dispatch Flat.engine rest
  | "tree" :: rest => dispatch TreeModel.engine rest
  | "both" :: rest => dispatch bothEngines rest
  | _ => dispatch bothEngines args
