/- Extract the theorem-dependency graph beneath the audited entrypoints.
   Roots: every `#print axioms` name in model/ProofAudit.lean, plus `extraRoots`
   (theorems worth browsing that are not audit entrypoints).
   Visible nodes: non-internal theorems in `RearmBarrier` modules (private ones included).
   Auxiliary decls (`_proof_`, matchers, eq lemmas) are inlined into their parent.
   Output: JSON to $DEPGRAPH_OUT (default depgraph.json). -/
import RearmBarrier
import Lean

open Lean

def projRoots : List Name := [`RearmBarrier]

/-- Unaudited theorems that get their own view in the map. -/
def extraRoots : Array Name := #[]

def auxComponent (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
  s.startsWith "eq_def" || s.startsWith "eq_" || s == "sizeOf_spec" ||
  s.startsWith "injEq" || s.startsWith "below" || s.startsWith "brecOn" ||
  s.startsWith "rec" || s.startsWith "casesOn" || s.startsWith "noConfusion" ||
  s.startsWith "induct" || s.startsWith "sizeOf" || s.startsWith "ibelow" ||
  s.startsWith "binduction"

/-- User-facing name: strips the `_private.<module>.0.` mangling. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

partial def run : CoreM Unit := do
  let env ← getEnv
  let auditPath := (← IO.getEnv "PROOF_AUDIT").getD "ProofAudit.lean"
  let audited : Array Name := ((← IO.FS.readFile auditPath).splitOn "\n").toArray.filterMap
    fun l => (l.trimAscii.toString.dropPrefix? "#print axioms ").map
      fun s => s.toString.trimAscii.toString.toName
  let modOf (n : Name) : Option Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]?
    | none => none
  let isProj (n : Name) : Bool :=
    match modOf n with
    | some m => projRoots.contains m.getRoot
    | none => false
  let isAuxName (n : Name) : Bool :=
    (userName n).components.any fun c => auxComponent c.toString
  let isVisible (n : Name) : Bool := Id.run do
    if !isProj n || isAuxName n then return false
    match env.find? n with
    | some (.thmInfo _) => return true
    | _ => return false
  -- memoized: visible theorem deps of any project constant, inlining aux decls
  let memoRef ← IO.mkRef (∅ : Std.HashMap Name (Array Name))
  let rec visDeps (n : Name) (stack : List Name) : CoreM (Array Name) := do
    if stack.contains n then return #[]
    if let some r := (← memoRef.get).get? n then return r
    let some ci := env.find? n | return #[]
    let valDeps := match ci with
      | .thmInfo t => t.value.getUsedConstants
      | .defnInfo d => d.value.getUsedConstants
      | _ => #[]
    let used := valDeps ++ ci.type.getUsedConstants
    let mut out : Array Name := #[]
    let mut seen : Std.HashSet Name := ∅
    for d in used do
      if seen.contains d then continue
      seen := seen.insert d
      if d == n then continue
      if isVisible d then
        out := out.push d
      else if isProj d then
        -- inline through aux theorems/defs that carry proofs (wf defs, matchers)
        match env.find? d with
        | some (.thmInfo _) | some (.defnInfo _) =>
          if isAuxName d then
            for x in (← visDeps d (n :: stack)) do
              if !seen.contains x then
                seen := seen.insert x
                out := out.push x
        | _ => pure ()
    memoRef.modify (·.insert n out)
    return out
  let roots := audited ++ extraRoots.filter (!audited.contains ·)
  -- BFS from the roots over visible theorems
  for r in roots do
    unless isVisible r do throwError "root {r} is not a visible project theorem"
  let mut queue := roots
  let mut nodes : Std.HashSet Name := Std.HashSet.ofArray roots
  let mut edges : Array (Name × Name) := #[]
  let mut i := 0
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    let deps ← visDeps n []
    for d in deps do
      edges := edges.push (n, d)
      if !nodes.contains d then
        nodes := nodes.insert d
        queue := queue.push d
  -- gather node metadata: module + declaration line span + statement
  let mut nodeJson : Array Json := #[]
  for n in queue do
    let m := (modOf n).getD .anonymous
    let rng ← findDeclarationRanges? n
    let (l0, l1) := match rng with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    let ty ← match env.find? n with
      | some ci => do
        let fmt ← Meta.MetaM.run' (Meta.ppExpr ci.type)
        pure (fmt.pretty 60)
      | none => pure ""
    nodeJson := nodeJson.push <| Json.mkObj
      [("name", Json.str (userName n).toString), ("module", Json.str m.toString),
       ("lines", Json.arr #[Json.num l0, Json.num l1]),
       ("type", Json.str ty), ("root", Json.bool (audited.contains n)),
       ("extra", Json.bool (extraRoots.contains n && !audited.contains n))]
  let edgeJson := edges.map fun (a, b) =>
    Json.arr #[Json.str (userName a).toString, Json.str (userName b).toString]
  let json := Json.mkObj [("nodes", Json.arr nodeJson), ("edges", Json.arr edgeJson)]
  IO.FS.writeFile ((← IO.getEnv "DEPGRAPH_OUT").getD "depgraph.json") json.pretty
  IO.println s!"roots={roots.size} nodes={queue.size} edges={edges.size}"

#eval run
