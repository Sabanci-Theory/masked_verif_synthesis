import Verif.«n-aryDAG»
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Circuit, Global DAG, Probe State, and Rewriting
-/

-- ============================================================
-- Wire-level types
-- ============================================================

/-- One input to a wire's defining gate. -/
inductive WireInput where
  | leaf  : VarType → WireInput
  | wire  : String  → WireInput
  | const : Bool    → WireInput
  deriving Repr, DecidableEq, Hashable, Inhabited

/-- The defining gate of a wire.  A single-input XOR is the "alias" case
    (the wire equals its single input). -/
inductive WireDef where
  | xor : Array WireInput → WireDef
  | and : Array WireInput → WireDef
  deriving Repr, Inhabited

namespace WireDef

@[inline]
def inputs : WireDef → Array WireInput
  | WireDef.xor i => i
  | WireDef.and i => i

@[inline]
def isXor : WireDef → Bool
  | WireDef.xor _ => true
  | WireDef.and _ => false

end WireDef

/-- A wire-level netlist.

    `wireOrder` lists the **probeable** gadget-body wires (the observable set).
    `inputOrder` lists **input shares** — atomically-encoded gadget inputs that
    are not probe targets but whose `WireDef` is kept so their algebraic value is
    available to the closure and (via the DAG) to the rewrite engine. -/
structure Circuit where
  wireOrder  : Array String           := #[]
  inputOrder : Array String           := #[]
  wireDefs   : HashMap String WireDef := {}
  deriving Inhabited

namespace Circuit

@[inline]
def hasWire (c : Circuit) (name : String) : Bool :=
  c.wireDefs.contains name

def addWire (c : Circuit) (name : String) (d : WireDef) : Circuit :=
  if c.hasWire name then c
  else { c with
    wireOrder := c.wireOrder.push name
    wireDefs  := c.wireDefs.insert name d }

/-- Record an input share: stored in `wireDefs` (so closure can see its value)
    and `inputOrder`, but never in `wireOrder`, so it is not enumerated as a
    probe target. -/
def addInput (c : Circuit) (name : String) (d : WireDef) : Circuit :=
  if c.hasWire name then c
  else { c with
    inputOrder := c.inputOrder.push name
    wireDefs   := c.wireDefs.insert name d }

def ppWireInput : WireInput → String
  | WireInput.leaf (VarType.Secret s) => s
  | WireInput.leaf (VarType.Random r) => r
  | WireInput.leaf (VarType.Public p) => s!"p({p})"
  | WireInput.wire name               => name
  | WireInput.const true              => "1"
  | WireInput.const false             => "0"

def ppWireDef (d : WireDef) : String :=
  let parts := d.inputs.toList.map ppWireInput
  let sep := if d.isXor then " + " else " * "
  String.intercalate sep parts

def ppLine (c : Circuit) (tag : String) (name : String) : String :=
  match c.wireDefs[name]? with
  | some d => s!"  {tag}{name} = {ppWireDef d}"
  | none   => s!"  {tag}{name} = ??"

def ppCircuit (c : Circuit) : String :=
  let inputs := c.inputOrder.toList.map (ppLine c "[in] ")
  let body   := c.wireOrder.toList.map (ppLine c "")
  String.intercalate "\n" (inputs ++ body)

end Circuit

-- ============================================================
-- Global DAG (Circuit + DAG + bridge)
-- ============================================================

structure GlobalDAG where
  dag     : DAG                   := {}
  circuit : Circuit               := {}
  wires   : HashMap String NodeId := {}
  deriving Inhabited

namespace GlobalDAG

-- high-level circuit-building API

/-- Resolve a `WireInput` to a NodeId, allocating in the DAG as needed.
    Wire references panic if the wire is undeclared. -/
def resolveInput (g : GlobalDAG) (inp : WireInput) : GlobalDAG × NodeId :=
  match inp with
  | WireInput.leaf v  =>
    let (d, id) := g.dag.mkLeaf v
    ({ g with dag := d }, id)
  | WireInput.const b =>
    let (d, id) := g.dag.mkConst b
    ({ g with dag := d }, id)
  | WireInput.wire name =>
    match g.wires[name]? with
    | some id => (g, id)
    | none    => panic! s!"resolveInput: undefined wire '{name}'"

/-- Resolve every input in order. -/
def resolveInputs (g : GlobalDAG) (inputs : Array WireInput) : GlobalDAG × Array NodeId :=
  inputs.foldl (fun (g, acc) inp =>
    let (g, id) := g.resolveInput inp
    (g, acc.push id))
    (g, #[])

/-- Declare a wire `name = XOR(inputs)`.  Records the WireDef in the Circuit,
    builds the corresponding DAG node, and registers wire→NodeId.

    **Faithfulness contract:** `inputs.size ≤ 2`.  The stored `Circuit` must be a
    faithful 2-ary netlist, because in the probing model every 2-input gate
    output is a distinct observable; an n-ary sum hides `n-2` intermediate
    observables and would make the probe enumeration unsound.  Callers must
    decompose n-ary sums into explicit named intermediates — and must choose the
    association themselves, since it is security-relevant (e.g. for DOM-AND the
    fresh mask must be grouped with a cross term, not added last). -/
def addWireXor (g : GlobalDAG) (name : String) (inputs : Array WireInput) : GlobalDAG :=
  if inputs.size > 2 then
    panic! s!"addWireXor: wire '{name}' has {inputs.size} inputs; gates must be 2-ary \
              (decompose into named intermediates; the association is security-relevant)"
  else if g.circuit.hasWire name then g
  else
    let (g, ids) := g.resolveInputs inputs
    let (dag, nid) := g.dag.mkXor ids
    { g with dag     := dag
             wires   := g.wires.insert name nid
             circuit := g.circuit.addWire name (WireDef.xor inputs) }

/-- Declare a wire `name = AND(inputs)`.  Same 2-ary faithfulness contract as
    `addWireXor`. -/
def addWireAnd (g : GlobalDAG) (name : String) (inputs : Array WireInput) : GlobalDAG :=
  if inputs.size > 2 then
    panic! s!"addWireAnd: wire '{name}' has {inputs.size} inputs; gates must be 2-ary"
  else if g.circuit.hasWire name then g
  else
    let (g, ids) := g.resolveInputs inputs
    let (dag, nid) := g.dag.mkAnd ids
    { g with dag     := dag
             wires   := g.wires.insert name nid
             circuit := g.circuit.addWire name (WireDef.and inputs) }

/-- Declare an *input share* `name = XOR(inputs)`: an atomically-encoded gadget
    input.  Unlike `addWireXor`/`addWireAnd` this is **not** a probe target
    (it is recorded in `circuit.inputOrder`, never `wireOrder`, so
    `checkDProbing` will not enumerate it) and is **exempt from the 2-ary rule**,
    because the encoding is given off-circuit and has no observable intermediate.

    Its expression still enters the DAG and its randoms/secrets are registered, so
    probes on the gadget *body* are verified against the full algebraic structure —
    e.g. a body wire `a0 * b0` resolves to `r_a * r_b` through the share defs. -/
def addShare (g : GlobalDAG) (name : String) (inputs : Array WireInput) : GlobalDAG :=
  if g.wires.contains name then g
  else
    let (g, ids) := g.resolveInputs inputs
    let (dag, nid) := g.dag.mkXor ids
    { g with dag     := dag
             wires   := g.wires.insert name nid
             circuit := g.circuit.addInput name (WireDef.xor inputs) }

end GlobalDAG

-- ============================================================
-- DFS, Probe State, rewrite engine
-- ============================================================

structure DFSState where
  xorParCount   : HashMap NodeId Nat            := {}
  totalParCount : HashMap NodeId Nat            := {}
  mulDepth      : HashMap NodeId Nat            := {}
  parents       : HashMap NodeId (Array NodeId) := {}
  visited       : HashMap NodeId Unit           := {}

partial def dfsChild (dag : DAG) (s : DFSState) (childId parentId : NodeId)
    (childDepth : Nat) (parentIsXor : Bool) : DFSState :=
  let tpc  := (s.totalParCount[childId]?).getD 0 + 1
  let xpc  := (s.xorParCount[childId]?).getD 0 + (if parentIsXor then 1 else 0)
  let d    := min childDepth ((s.mulDepth[childId]?).getD (childDepth + 1))
  let pars := ((s.parents[childId]?).getD #[]).push parentId
  let s := { s with
    totalParCount := s.totalParCount.insert childId tpc
    xorParCount   := s.xorParCount.insert   childId xpc
    mulDepth      := s.mulDepth.insert      childId d
    parents       := s.parents.insert       childId pars }
  if s.visited.contains childId then s
  else
    let s := { s with visited := s.visited.insert childId () }
    match dag.kind? childId with
    | some (NodeKind.xorNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid childId d       true)  s
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid childId (d + 1) false) s
    | _ => s

partial def dfsRoot (dag : DAG) (s : DFSState) (rootId : NodeId) : DFSState :=
  if s.visited.contains rootId then s
  else
    let s := { s with
      visited  := s.visited.insert rootId ()
      mulDepth := s.mulDepth.insert rootId 0 }
    match dag.kind? rootId with
    | some (NodeKind.xorNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid rootId 0 true)  s
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid rootId 1 false) s
    | _ => s

structure ProbeState where
  roots            : Array NodeId
  /-- The probe roots as a set.  Needed to keep *observed* nodes out of the
      simple-rule worklist: relabeling a random that is itself a probe root is
      unsound (conditioned on the observed `r`, `x = e+r` is not fresh). -/
  rootSet          : HashMap NodeId Unit
  xorParCount      : HashMap NodeId Nat
  totalParCount    : HashMap NodeId Nat
  mulDepth         : HashMap NodeId Nat
  parents          : HashMap NodeId (Array NodeId)
  todo             : Array NodeId
  rewrittenRandoms : HashMap NodeId Unit
  deriving Inhabited

namespace ProbeState

@[inline]
def isRandom (ps : ProbeState) (dag : DAG) (id : NodeId) : Bool :=
  ps.rewrittenRandoms.contains id ||
  match dag.kind? id with
  | some (NodeKind.leaf (VarType.Random _)) => true
  | _                                       => false

end ProbeState

def insertTodoByDepth (ps : ProbeState) (r : NodeId) : ProbeState :=
  if ps.todo.contains r then ps
  else
    let d := (ps.mulDepth[r]?).getD 0
    let pos := (ps.todo.findIdx? (fun rid => (ps.mulDepth[rid]?).getD 0 > d)).getD ps.todo.size
    { ps with todo := ps.todo.insertIdx! pos r }

/-- Probe initialisation by root NodeIds: run the DFS over the given roots and
    collect the simple-rule worklist `todo` (randoms with a unique additive
    occurrence).  Does **not** factor — factoring is applied lazily by the caller
    (`checkProbeRoots`), only after the simple rule has failed on the current form. -/
def initProbeByIds (g : GlobalDAG) (rootIds : Array NodeId) : GlobalDAG × ProbeState :=
  let s : DFSState := rootIds.foldl (dfsRoot g.dag) {}
  let rootSet : HashMap NodeId Unit := rootIds.foldl (fun m r => m.insert r ()) {}
  let todoUnsorted := g.dag.randoms.filter (fun rId =>
    s.totalParCount[rId]? == some 1 && s.xorParCount[rId]? == some 1 && !rootSet.contains rId)
  let todo := todoUnsorted.qsort (fun a b => (s.mulDepth[a]?).getD 0 < (s.mulDepth[b]?).getD 0)
  (g, {
    roots            := rootIds
    rootSet          := rootSet
    xorParCount      := s.xorParCount
    totalParCount    := s.totalParCount
    mulDepth         := s.mulDepth
    parents          := s.parents
    todo             := todo
    rewrittenRandoms := {} })

def isSecure (g : GlobalDAG) (ps : ProbeState) : Bool :=
  ps.roots.all (fun rid => !(g.dag.isSecretNode rid)) &&
  g.dag.secrets.all (fun sid => (ps.totalParCount[sid]?).getD 0 == 0)

partial def decrementParent (dag : DAG) (ps : ProbeState) (nodeId : NodeId) (wasXor : Bool)
    : ProbeState :=
  let tpc := (ps.totalParCount[nodeId]?).getD 0
  if tpc == 0 then ps
  else
    let xpc  := (ps.xorParCount[nodeId]?).getD 0
    let tpc' := tpc - 1
    let xpc' := if wasXor && xpc > 0 then xpc - 1 else xpc
    let ps := { ps with
      totalParCount := if tpc' == 0 then ps.totalParCount.erase nodeId
                       else ps.totalParCount.insert nodeId tpc'
      xorParCount   := if tpc' == 0 then ps.xorParCount.erase nodeId
                       else ps.xorParCount.insert nodeId xpc' }
    if tpc' == 0 then
      let ps := { ps with todo := ps.todo.filter (· != nodeId) }
      if ps.rewrittenRandoms.contains nodeId then ps
      else
        match dag.kind? nodeId with
        | some (NodeKind.xorNode ch) =>
          ch.foldl (fun acc cid =>
            let acc := { acc with
            parents := acc.parents.insert cid (((acc.parents[cid]?).getD #[]).filter (· != nodeId)) }
            decrementParent dag acc cid true) ps
        | some (NodeKind.andNode ch) =>
          ch.foldl (fun acc cid =>
            let acc := { acc with
            parents := acc.parents.insert cid (((acc.parents[cid]?).getD #[]).filter (· != nodeId)) }
            decrementParent dag acc cid false) ps
        | _ => ps
    else
      -- Cascade re-insertion.  The `rootSet` check mirrors `initProbeByIds` (and
      -- `findSimpleRandom`'s in the general loop): a random that is itself a probe
      -- ROOT must never be relabeled by the simple rule — its value is observed,
      -- so conditioned on it, `x = e+r` is not uniform and marking `x` fresh
      -- hides secrets the tuple actually exposes (false SECURE; see
      -- TestRootBug.lean's `(r, s+r, r+r3)`).  Such tuples fall through to the
      -- complete general loop, which substitutes roots correctly.
      if ps.isRandom dag nodeId && !ps.rootSet.contains nodeId
         && tpc' == 1 && xpc' == 1 then insertTodoByDepth ps nodeId
      else ps

/-- Fire the simple rule on random `r`: splice its unique additive parent `x`
    away and drop `r`.

    NOTE: this tier does **not** surface a coupling.  The semantic relabel of a
    step is `r ← x` (`x = e+r`), but a *cascade* step fires on a
    `rewrittenRandoms` node `x` (not a tape variable), and the pair `(x, x₂)` is
    not a tape relabel: replaying it by node substitution diverges from the
    certified derivation (occurrences of `x` that collapsed to `r` are missed),
    and `evalCoupledEnv` ignores `env` bindings at non-leaf ids entirely.
    Couplings for the extension come from `checkProbeCompleteT`, whose steps are
    always leaf relabels (DECISIONS.md 2026-07-01). -/
def applyRewrite (g : GlobalDAG) (ps : ProbeState) (r : NodeId)
    : GlobalDAG × ProbeState :=
  let x := ((ps.parents[r]?).getD #[])[0]!
  let xCh := match g.dag.kind? x with
    | some (NodeKind.xorNode ch) => ch
    | _                          => #[]
  let ps := { ps with rewrittenRandoms := ps.rewrittenRandoms.insert x () }
  let ps := { ps with
    totalParCount := ps.totalParCount.erase r
    xorParCount   := ps.xorParCount.erase   r
    mulDepth      := ps.mulDepth.erase      r
    parents       := ps.parents.erase       r }
  let ps := xCh.foldl (fun ps ci =>
    if ci == r then ps
    else
      let newPars := ((ps.parents[ci]?).getD #[]).filter (· != x)
      let ps := { ps with parents := ps.parents.insert ci newPars }
      decrementParent g.dag ps ci true)
    ps
  (g, ps)

partial def rewriteLoop (g : GlobalDAG) (ps : ProbeState)
    : GlobalDAG × ProbeState × Bool :=
  if isSecure g ps then (g, ps, true)
  else
    match ps.todo[0]? with
    | none   => (g, ps, false)
    | some r =>
      let ps := { ps with todo := ps.todo.eraseIdx! 0 }
      let (g', ps') := applyRewrite g ps r
      rewriteLoop g' ps'

-- ============================================================
-- Complete fallback: full optimistic sampling (simple + general rule)
--
-- The reference-counted `rewriteLoop` above only fires the *simple* rule
-- (eliminate a random with a unique additive occurrence).  That is sound but
-- incomplete: it cannot certify tuples where the masking randoms each occur in
-- two observations and a *linear dependency* between observations is needed to
-- isolate one (e.g. high-order DOM-AND, where consecutive output partial sums
-- differ by one masked cross-term).
--
-- This fallback implements the general rule by *actual substitution* on the
-- explicit observation tuple: pick a random `r` and an additive occurrence
-- `x1 = e + r` with `r ∉ vars(e)`, then substitute `r ← e+r` everywhere.  By the
-- optimistic-sampling lemma this preserves the joint distribution; `mkXor`
-- re-canonicalisation makes the matched occurrence collapse to a bare `r` while
-- every other occurrence absorbs `e` (cancelling where they share it).  The
-- simple rule is the special case where `r` occurs once; we try it first.
--
-- Termination: each general substitution retires one random into `used` and is
-- never repeated for it (|used| ≤ #randoms); between general steps the simple
-- rule strictly shrinks the tuple.  `fuel` is a safety net — exhausting it
-- returns `false` (sound: only ever a false negative, never a false "secure").
-- ============================================================

/-- Does any `Secret` leaf occur in the sub-DAG rooted at `n`? -/
partial def reachesSecretAux (dag : DAG) (vis : HashMap NodeId Bool) (n : NodeId)
    : HashMap NodeId Bool × Bool :=
  match vis[n]? with
  | some b => (vis, b)
  | none   =>
    match dag.kind? n with
    | some (NodeKind.leaf (VarType.Secret _)) => (vis.insert n true, true)
    | some (NodeKind.xorNode ch)
    | some (NodeKind.andNode ch) =>
      let (vis, b) := ch.foldl (fun (v, acc) c =>
        if acc then (v, true) else reachesSecretAux dag v c) (vis, false)
      (vis.insert n b, b)
    | _ => (vis.insert n false, false)

/-- Probing `Test`: is the whole tuple free of secrets? -/
def tupleHasSecret (dag : DAG) (tuple : Array NodeId) : Bool :=
  (tuple.foldl (fun (v, acc) r =>
    if acc then (v, true) else reachesSecretAux dag v r)
    (({} : HashMap NodeId Bool), false)).2

/-- Is `target` reachable from `n` (does `n`'s sub-DAG mention `target`)?  Used to
    enforce the side-condition `r ∉ vars(e)`. -/
partial def reachesNodeAux (dag : DAG) (target : NodeId) (vis : HashMap NodeId Bool) (n : NodeId)
    : HashMap NodeId Bool × Bool :=
  if n == target then (vis, true)
  else match vis[n]? with
  | some b => (vis, b)
  | none   =>
    match dag.kind? n with
    | some (NodeKind.xorNode ch)
    | some (NodeKind.andNode ch) =>
      let (vis, b) := ch.foldl (fun (v, acc) c =>
        if acc then (v, true) else reachesNodeAux dag target v c) (vis, false)
      (vis.insert n b, b)
    | _ => (vis.insert n false, false)

@[inline]
def nodeReaches (dag : DAG) (target n : NodeId) : Bool :=
  (reachesNodeAux dag target ({} : HashMap NodeId Bool) n).2

/-- Substitute leaf `r` by node `t` (= `e+r`) throughout `n`, single level (never
    descending into `t`).  Memoised; `mkXor`/`mkAnd` re-canonicalise. -/
partial def substNode (g : GlobalDAG) (r t : NodeId) (memo : HashMap NodeId NodeId) (n : NodeId)
    : GlobalDAG × HashMap NodeId NodeId × NodeId :=
  if n == r then (g, memo, t)
  else match memo[n]? with
  | some m => (g, memo, m)
  | none   =>
    match g.dag.kind? n with
    | some (NodeKind.xorNode ch) =>
      let (g, memo, ch') := ch.foldl (fun (g, memo, acc) c =>
        let (g, memo, c') := substNode g r t memo c
        (g, memo, acc.push c')) (g, memo, #[])
      let (dag, m) := g.dag.mkXor ch'
      ({ g with dag }, memo.insert n m, m)
    | some (NodeKind.andNode ch) =>
      let (g, memo, ch') := ch.foldl (fun (g, memo, acc) c =>
        let (g, memo, c') := substNode g r t memo c
        (g, memo, acc.push c')) (g, memo, #[])
      let (dag, m) := g.dag.mkAnd ch'
      ({ g with dag }, memo.insert n m, m)
    | _ => (g, memo.insert n n, n)

/-- Apply `r ← e+r` to every root (`e` given as a node).  Also returns the
    substitution node `t = e+r`, so the caller can record the coupling step
    `(r, t)` for replay on wires outside the tuple. -/
def substTupleByE (g : GlobalDAG) (tuple : Array NodeId) (r e : NodeId)
    : GlobalDAG × Array NodeId × NodeId :=
  let (dag, t) := g.dag.mkXor #[e, r]
  let g := { g with dag }
  let (g, _, roots) := tuple.foldl (fun (g, memo, acc) root =>
    let (g, memo, root') := substNode g r t memo root
    (g, memo, acc.push root')) (g, ({} : HashMap NodeId NodeId), #[])
  (g, roots, t)

/-- `e` for an additive occurrence `x1 = e + r`: `x1`'s other children.
    `x1` must be a XOR node (both find-rules guarantee it).  Anything else is a
    hard error: falling back to `e := x1` would return a context *containing*
    `r`, making the relabel `r ← e+r` non-bijective — a silent soundness hole. -/
def contextOf (g : GlobalDAG) (x1 r : NodeId) : GlobalDAG × NodeId :=
  match g.dag.kind? x1 with
  | some (NodeKind.xorNode ch) =>
    let (dag, e) := g.dag.mkXor (ch.filter (· != r))
    ({ g with dag }, e)
  | _ => panic! s!"contextOf: node {x1} is not a xorNode — additive occurrence \
                   expected (a non-XOR context would make r ← e+r non-bijective)"

/-- Simple-rule candidate: a random occurring exactly once, additively, not a
    root.  Among candidates prefer the least multiplicative depth (the additive
    layer first), matching the fast path and maskVerif's increasing-depth order. -/
def findSimpleRandom (randoms : Array NodeId) (s : DFSState) (rootSet : HashMap NodeId Unit)
    : Option (NodeId × NodeId) := Id.run do
  let mut best : Option (NodeId × NodeId × Nat) := none
  for r in randoms do
    if rootSet.contains r then continue
    if s.totalParCount[r]? == some 1 && s.xorParCount[r]? == some 1 then
      let x1 := ((s.parents[r]?).getD #[])[0]!
      let d  := (s.mulDepth[r]?).getD 0
      match best with
      | none            => best := some (r, x1, d)
      | some (_, _, bd) => if d < bd then best := some (r, x1, d)
  return best.map (fun (r, x1, _) => (r, x1))

/-- General-rule candidate: a not-yet-used random occurring ≥ 2× that has an
    additive parent `x1` whose other children do not mention it.  Prefer the
    greatest multiplicative depth. -/
def findGeneralRandom (dag : DAG) (randoms : Array NodeId) (s : DFSState)
    (rootSet used : HashMap NodeId Unit)
    : Option (NodeId × NodeId) := Id.run do
  let mut best : Option (NodeId × NodeId × Nat) := none
  for r in randoms do
    if used.contains r then continue
    let occ := (s.totalParCount[r]?).getD 0 + (if rootSet.contains r then 1 else 0)
    if occ < 2 then continue
    if (s.xorParCount[r]?).getD 0 == 0 then continue
    -- `reachesNodeAux`'s memo is keyed by node for a *fixed* target `r`, so we can
    -- share one `vis` across all of `r`'s additive parents and their children
    -- instead of re-walking the sub-DAG from scratch on every check.
    let mut vis : HashMap NodeId Bool := {}
    let mut chosen : Option NodeId := none
    for x1 in (s.parents[r]?).getD #[] do
      if chosen.isSome then continue
      match dag.kind? x1 with
      | some (NodeKind.xorNode ch) =>
        let mut clear := true
        for c in ch do
          if clear && c != r then
            let (vis', reaches) := reachesNodeAux dag r vis c
            vis := vis'
            if reaches then clear := false
        if clear then chosen := some x1
      | _ => pure ()
    match chosen with
    | none    => pure ()
    | some x1 =>
      let d := (s.mulDepth[r]?).getD 0
      match best with
      | none            => best := some (r, x1, d)
      | some (_, _, bd) => if d < bd then best := some (r, x1, d)
  return best.map (fun (r, x1, _) => (r, x1))

/-- Full optimistic-sampling loop: simple rule first, then the general rule;
    succeeds when no secret remains.  Factoring is **lazy**: each round the finds
    run on the current (canonical, possibly unfactored) form; only when *both*
    finds stall do we factor and retry.  `factored` tracks whether the current
    form has already been factored since the last substitution, so we declare
    failure only after the finds stall on the *factored* form.  Each substitution
    resets `factored := false` (the new form is unfactored). -/
partial def rewriteComplete (g : GlobalDAG) (tuple : Array NodeId)
    (used : HashMap NodeId Unit) (fuel : Nat) (factored : Bool)
    (coupling : Array (NodeId × NodeId)) : GlobalDAG × Bool × Array (NodeId × NodeId) :=
  -- One DFS pass per round serves two purposes: it answers "is the tuple
  -- secret-free?" (no separate `tupleHasSecret` traversal — a secret survives iff
  -- it is a root or has a parent in the explored sub-DAG) and it feeds the finds.
  let s : DFSState := tuple.foldl (dfsRoot g.dag) {}
  let secretFree :=
    tuple.all (fun rid => !g.dag.isSecretNode rid) &&
    g.dag.secrets.all (fun sid => (s.totalParCount[sid]?).getD 0 == 0)
  if secretFree then (g, true, coupling)
  else if fuel == 0 then (g, false, coupling)
  else
    let rootSet : HashMap NodeId Unit := tuple.foldl (fun m r => m.insert r ()) {}
    -- Restrict the finds to the randoms actually present in this tuple rather than
    -- scanning every random in the circuit each round.
    let tupleRandoms := g.dag.randoms.filter (fun r =>
      (s.totalParCount[r]?).getD 0 > 0 || rootSet.contains r)
    match findSimpleRandom tupleRandoms s rootSet with
    | some (r, x1) =>
      let (g, e)         := contextOf g x1 r
      let (g, tuple', t) := substTupleByE g tuple r e
      rewriteComplete g tuple' used (fuel - 1) false (coupling.push (r, t))
    | none =>
      match findGeneralRandom g.dag tupleRandoms s rootSet used with
      | some (r, x1) =>
        let (g, e)         := contextOf g x1 r
        let (g, tuple', t) := substTupleByE g tuple r e
        rewriteComplete g tuple' (used.insert r ()) (fuel - 1) false (coupling.push (r, t))
      | none =>
        -- Both finds stalled.  If the form is already factored, give up;
        -- otherwise factor (to expose product-buried randoms) and retry.
        if factored then (g, false, coupling)
        else
          let (dag, tuple') := g.dag.factor tuple
          rewriteComplete { g with dag } tuple' used fuel true coupling

/-- Entry point for the complete checker on a tuple of observation roots.
    Returns the coupling `T` (ordered `(r, t)` substitutions) used to certify it. -/
def checkProbeCompleteT (g : GlobalDAG) (tuple : Array NodeId)
    : GlobalDAG × Bool × Array (NodeId × NodeId) :=
  rewriteComplete g tuple {} ((g.dag.randoms.size + 2) * 256) false #[]

/-- Verdict-only probe check with lazy factoring:
    (1) reference-counted simple rule on the **unfactored** roots;
    (2) on failure, factor and retry the simple rule;
    (3) on failure, the complete general loop, which itself factors lazily
        (only when both find-rules stall — see `rewriteComplete`).
    Factoring widens the certifiable class but is costly, so it is paid for only
    when the cheaper simple rule cannot discharge the probe.

    Deliberately does **not** return a coupling: the reference-counted tiers'
    cascade steps are not tape relabels (see `applyRewrite`), so their recorded
    pairs would not be replayable by `substNode`/`evalCoupledEnv`.  Discharges
    that need the certifying coupling `T` for the extension must use
    `checkProbeCompleteT` directly (as `checkChosenCoupling` does). -/
def checkProbeRoots (g : GlobalDAG) (rootIds : Array NodeId) : GlobalDAG × Bool :=
  let (g, ps)       := initProbeByIds g rootIds
  let (g, ps, sec)  := rewriteLoop g ps
  if sec then (g, true)
  else
    let (dag, froots) := g.dag.factor ps.roots
    let g := { g with dag }
    let (g, ps2)      := initProbeByIds g froots
    let (g, _, sec2)  := rewriteLoop g ps2
    if sec2 then (g, true)
    else
      let (g, sec3, _) := checkProbeCompleteT g rootIds
      (g, sec3)

partial def evalNode (dag : DAG) (env : Array UInt64) (n : NodeId) (cache : Array (Option UInt64))
    : Array (Option UInt64) × UInt64 :=
  match cache[n]! with
  | some v => (cache, v)
  | none =>
    let (cache, v) := match dag.kind? n with
      | some (NodeKind.constVal b) => (cache, if b then 0xFFFFFFFFFFFFFFFF else 0)
      -- All leaves (Secret, Random, AND Public) read their lanes from `env`.
      -- Publics must stay symbolic here: evaluating them as a constant would
      -- blind the PIT to secret-dependence that only shows jointly with a
      -- public (e.g. `s·p` at `p = 0`), wasting exact-phase calls.
      | some (NodeKind.leaf _) => (cache, env[n]!)
      | some (NodeKind.xorNode ch) =>
        ch.foldl (fun (c, acc) chId =>
          let (c, vCh) := evalNode dag env chId c
          (c, acc ^^^ vCh)) (cache, 0)
      | some (NodeKind.andNode ch) =>
        ch.foldl (fun (c, acc) chId =>
          let (c, vCh) := evalNode dag env chId c
          (c, acc &&& vCh)) (cache, 0xFFFFFFFFFFFFFFFF)
      | _ => (cache, 0)
    (cache.set! n v, v)

/-- Coupled random environment: bind each random `r` to the value of its *net*
    image `σ(r)` under the whole coupling, so that `eval(w, env) = eval(w∘T)`.
    Since `σ(r_k) = σ_{>k}(e_k) + r_k`, the later substitutions must already be in
    `env` when we process `r_k` — hence **reverse** (right-to-left) folding.  Each
    step sets `env[r] := eval(e+r)` (`rt.2 = e+r`); no extra XOR (that was the
    `r ← e` collapse bug). -/
def evalCoupledEnv (dag : DAG) (coupling : Array (NodeId × NodeId)) (initialEnv : Array UInt64)
    : Array UInt64 :=
  coupling.foldr (fun rt env =>
    let cache : Array (Option UInt64) := (List.replicate dag.nextId none).toArray
    let (_, ve) := evalNode dag env rt.2 cache
    env.set! rt.1 ve)
    initialEnv

/-- splitmix64 finalizer.  The raw state of a power-of-two-modulus LCG must not
    be used as PIT lanes directly: bit `k` of the state has period `2^(k+1)`
    (bit 0 alternates, bit 1 cycles with period 4, …), so the low lanes assign
    leaves highly structured, colliding values and carry almost no rejection
    power.  Mixing makes every output bit a pseudo-random function of the whole
    state, so all 64 lanes reject independently. -/
@[inline]
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

def mkEnv (dag : DAG) (secretsZero : Bool) : Array UInt64 := Id.run do
  let mut env := (List.replicate dag.nextId 0).toArray
  let mut seed : UInt64 := 0xDEADBEEFCAFEBAB0
  for i in [0:dag.nextId] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let v := mix64 seed
    if dag.isSecretNode i then
      env := env.set! i (if secretsZero then 0 else v)
    else
      env := env.set! i v
  env

-- ============================================================
-- ANF (algebraic normal form) — exact secret-freeness fallback
--
-- A monomial is a sorted, distinct array of leaf NodeIds (a multilinear product).
-- An ANF is a set of monomials (F2 polynomial), keyed by canonical string; two
-- equal monomials cancel.  Used when the syntactic `tupleHasSecret` cannot see a
-- product-cancellation that the coupling induced (the case where our XOR-only
-- replay under-detects vs the true, expanded polynomial).
-- ============================================================

/-- Sorted union of two monomials (`x·x = x`, so repeated variables collapse). -/
def monoUnion (a b : Array NodeId) : Array NodeId :=
  let sorted := (a ++ b).qsort (· < ·)
  sorted.foldl (fun acc x =>
    if acc.isEmpty || acc[acc.size - 1]! != x then acc.push x else acc) #[]

@[inline] def monoKey (m : Array NodeId) : String :=
  String.intercalate "," (m.toList.map toString)

/-- Toggle a monomial into an ANF set (F2: two copies cancel). -/
@[inline] def anfToggle (s : HashMap String (Array NodeId)) (m : Array NodeId)
    : HashMap String (Array NodeId) :=
  let k := monoKey m
  if s.contains k then s.erase k else s.insert k m

/-- XOR (symmetric difference) of two ANF sets. -/
def anfXor (a b : HashMap String (Array NodeId)) : HashMap String (Array NodeId) :=
  b.fold (fun acc _ m => anfToggle acc m) a

/-- Product of two ANF sets: distribute, unioning each monomial pair. -/
def anfAnd (a b : HashMap String (Array NodeId)) : HashMap String (Array NodeId) :=
  a.fold (fun acc _ mp =>
    b.fold (fun acc _ mq => anfToggle acc (monoUnion mp mq)) acc)
    ({} : HashMap String (Array NodeId))

/-- Full ANF of `n` over its leaves, memoised by NodeId. -/
partial def toANF (dag : DAG) (memo : HashMap NodeId (HashMap String (Array NodeId)))
    (n : NodeId) : HashMap NodeId (HashMap String (Array NodeId)) × HashMap String (Array NodeId) :=
  match memo[n]? with
  | some a => (memo, a)
  | none   =>
    let (memo, a) := match dag.kind? n with
      | some (NodeKind.constVal false) => (memo, ({} : HashMap String (Array NodeId)))
      | some (NodeKind.constVal true)  =>
        (memo, (({} : HashMap String (Array NodeId)).insert "" #[]))
      | some (NodeKind.leaf _) =>
        (memo, (({} : HashMap String (Array NodeId)).insert (monoKey #[n]) #[n]))
      | some (NodeKind.xorNode ch) =>
        ch.foldl (fun (m, acc) c =>
          let (m, ac) := toANF dag m c
          (m, anfXor acc ac)) (memo, ({} : HashMap String (Array NodeId)))
      | some (NodeKind.andNode ch) =>
        ch.foldl (fun (m, acc) c =>
          let (m, ac) := toANF dag m c
          (m, anfAnd acc ac)) (memo, (({} : HashMap String (Array NodeId)).insert "" #[]))
      | _ => (memo, ({} : HashMap String (Array NodeId)))
    (memo.insert n a, a)

/-- Exact secret-freeness via ANF: `w` is secret-free iff no surviving monomial of
    its ANF contains a `Secret` leaf.  Sound *and* complete (ANF is the canonical
    F2 form), so this catches the product-cancellations the syntactic
    `tupleHasSecret` misses. -/
def anfSecretFree (dag : DAG) (w : NodeId) : Bool :=
  let (_, anf) := toANF dag ({} : HashMap NodeId (HashMap String (Array NodeId))) w
  anf.fold (fun free _ m => free && !m.any (fun id => dag.isSecretNode id)) true

/-- **Coupling-driven probe-set extension.**  Given the coupling `T` and the
    candidate observations `(name, node)`, return the names whose `w∘T` is
    secret-free — the certified-safe set `ŷ`.  `T` is a composition of
    measure-preserving relabels `r ← e+r`, so any wire it blinds joins the safe
    set (every subset stays `d`-probing secure).

    `chosen` is force-included (its joint secret-freeness is the engine's verdict;
    this is also what keeps `unsafeWires = wires \ safe` shrinking → termination).
    Each other candidate is decided **exactly**, in three phases:
      1. PIT fast-reject — a bit-sliced F2 identity test on the coupled env; a lane
         disagreement means genuine secret-dependence (sound to reject).
      2. syntactic `substNode`+`tupleHasSecret` (XOR-canonicalisation only);
      3. ANF fallback (`anfSecretFree`) — exact, catches the product-cancellations
         phase 2 misses.  Acceptance never rests on the probabilistic PIT. -/
def couplingExtend (g : GlobalDAG) (coupling : Array (NodeId × NodeId))
    (chosen : Array String) (candidates : Array (String × NodeId))
    : GlobalDAG × Array String × Nat :=
  let chosenSet : HashMap String Unit := chosen.foldl (fun m w => m.insert w ()) {}
  let envRandFinal := evalCoupledEnv g.dag coupling (mkEnv g.dag false)
  let envZeroFinal := evalCoupledEnv g.dag coupling (mkEnv g.dag true)
  let (g, blinded, anfCount) := candidates.foldl (fun (acc : GlobalDAG × Array String × Nat) c =>
    let (g, keep, anfCount) := acc
    if chosenSet.contains c.1 then (g, keep.push c.1, anfCount)
    else
      -- Phase 1: PIT fast-reject.  A lane disagreement between secrets-random and
      -- secrets-zero witnesses genuine secret-dependence, so rejecting is sound
      -- (it can only cost yield if the env is imperfect, never admit a bad wire).
      let (_, valRand) := evalNode g.dag envRandFinal c.2 ((List.replicate g.dag.nextId none).toArray)
      let (_, valZero) := evalNode g.dag envZeroFinal c.2 ((List.replicate g.dag.nextId none).toArray)
      if valRand != valZero then
        (g, keep, anfCount)
      else
        -- Acceptance is EXACT.  Apply T (`w' = w∘T`), then:
        --   Phase 2: syntactic `tupleHasSecret` (fast, XOR-canonicalisation only);
        --   Phase 3: ANF fallback (exact, catches product-cancellations Phase 2 misses).
        let (g, w') := coupling.foldl
          (fun (st : GlobalDAG × NodeId) rt =>
            let (g, cur) := st
            let (g, _, cur') := substNode g rt.1 rt.2 ({} : HashMap NodeId NodeId) cur
            (g, cur'))
          (g, c.2)
        if !tupleHasSecret g.dag #[w'] then (g, keep.push c.1, anfCount)
        else if anfSecretFree g.dag w' then (g, keep.push c.1, anfCount + 1)
        else (g, keep, anfCount)) (g, #[], 0)
  (g, blinded, anfCount)

end verif
