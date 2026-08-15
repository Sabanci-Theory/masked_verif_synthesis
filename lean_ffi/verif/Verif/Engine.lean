import Verif.Circuit

namespace verif

open Std (HashMap)

/-!
# Rewrite Engine — optimistic sampling

Two implementations of the same rule set over a probe tuple's sub-DAG:

* the **reference-counted fast path** (`ProbeState`, `rewriteLoop`): the simple
  rule (eliminate a random with a unique additive occurrence) applied to
  fixpoint by incremental parent-count bookkeeping, never rewriting the DAG.
  Verdict-only — its cascade steps are not tape relabels (see `applyRewrite`),
  so it surfaces no coupling.  Used for the large union discharges.
* the **complete general loop** (`rewriteComplete`): simple + general rule by
  actual substitution (`substTuple`), with lazy stall-triggered factoring.
  Certifies everything the fast path does and returns the coupling `T`
  (`checkProbeCompleteT`), consumed by the extension in `Coupling.lean`.

`checkProbeRoots` is the tiered verdict-only entry point:
simple-unfactored → factor + simple → general loop.
-/

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
  -- `mulDepth` is the min over the paths seen *so far*, but a node's descendants
  -- are only explored on its first visit — a later, shallower path updates the
  -- node itself, not what lies below it.  So depths under a reconverging node
  -- can be overestimates.  Fine: only the ordering heuristics consume it.
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

/-- Memoised DFS: does any node in the sub-DAG rooted at `n` satisfy `p`?
    The memo `vis` is keyed by node for a *fixed* `p`, so callers checking many
    roots against one predicate can share it across calls.  Both reachability
    questions of the engine are instances: secret-freeness (`p = isSecretNode`)
    and the side-condition `r ∉ vars(e)` (`p = (· == r)`). -/
partial def anyNodeAux (dag : DAG) (p : NodeId → Bool) (vis : HashMap NodeId Bool) (n : NodeId)
    : HashMap NodeId Bool × Bool :=
  if p n then (vis, true)
  else match vis[n]? with
  | some b => (vis, b)
  | none   =>
    match dag.kind? n with
    | some (NodeKind.xorNode ch)
    | some (NodeKind.andNode ch) =>
      let (vis, b) := ch.foldl (fun (v, acc) c =>
        if acc then (v, true) else anyNodeAux dag p v c) (vis, false)
      (vis.insert n b, b)
    | _ => (vis.insert n false, false)

/-- Probing `Test`: is the whole tuple free of secrets? -/
def tupleHasSecret (dag : DAG) (tuple : Array NodeId) : Bool :=
  (tuple.foldl (fun (v, acc) r =>
    if acc then (v, true) else anyNodeAux dag dag.isSecretNode v r)
    (({} : HashMap NodeId Bool), false)).2

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

/-- Apply the relabel `r ← t` to every root, sharing one `substNode` memo across
    the whole tuple.

    `t` is the matched additive occurrence `x1 = e + r` **itself**: rebuilding
    `t = mkXor #[e, r]` from a separately constructed context `e` (as an earlier
    version did) is an identity — `x1`'s canonical child set *is* `e`'s children
    plus `r`, so hash-consing re-interns the rebuilt node to `x1`.  Substituting
    `r ← x1` directly therefore skips allocating `e` entirely.  Canonicalisation
    does the rest: the matched occurrence collapses to a bare `r`
    (`x1[r := x1]` flattens to `e + e + r = r`) and every other occurrence of
    `r` absorbs `e`. -/
def substTuple (g : GlobalDAG) (tuple : Array NodeId) (r t : NodeId)
    : GlobalDAG × Array NodeId :=
  let (g, _, roots) := tuple.foldl
    (fun (acc : GlobalDAG × HashMap NodeId NodeId × Array NodeId) root =>
      let (g, memo, rs) := acc
      let (g, memo, root') := substNode g r t memo root
      (g, memo, rs.push root'))
    (g, ({} : HashMap NodeId NodeId), #[])
  (g, roots)

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
    additive parent `x1` whose other children do not mention it.  Among
    candidates prefer the **least** multiplicative depth, mirroring
    `findSimpleRandom` (the benchmarks reflect this order; preferring the
    greatest depth was considered and never implemented). -/
def findGeneralRandom (dag : DAG) (randoms : Array NodeId) (s : DFSState)
    (rootSet used : HashMap NodeId Unit)
    : Option (NodeId × NodeId) := Id.run do
  let mut best : Option (NodeId × NodeId × Nat) := none
  for r in randoms do
    if used.contains r then continue
    let occ := (s.totalParCount[r]?).getD 0 + (if rootSet.contains r then 1 else 0)
    if occ < 2 then continue
    if (s.xorParCount[r]?).getD 0 == 0 then continue
    -- `anyNodeAux`'s memo is keyed by node for a *fixed* predicate (here
    -- `(· == r)`), so we can share one `vis` across all of `r`'s additive
    -- parents and their children instead of re-walking the sub-DAG from
    -- scratch on every check.
    let mut vis : HashMap NodeId Bool := {}
    let mut chosen : Option NodeId := none
    for x1 in (s.parents[r]?).getD #[] do
      if chosen.isSome then continue
      match dag.kind? x1 with
      | some (NodeKind.xorNode ch) =>
        let mut clear := true
        for c in ch do
          if clear && c != r then
            let (vis', reaches) := anyNodeAux dag (· == r) vis c
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
    (coupling : Array (NodeId × NodeId)) (allowFactor : Bool := true)
    : GlobalDAG × Bool × Array (NodeId × NodeId) :=
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
      let (g, tuple') := substTuple g tuple r x1
      rewriteComplete g tuple' used (fuel - 1) false (coupling.push (r, x1)) allowFactor
    | none =>
      match findGeneralRandom g.dag tupleRandoms s rootSet used with
      | some (r, x1) =>
        let (g, tuple') := substTuple g tuple r x1
        rewriteComplete g tuple' (used.insert r ()) (fuel - 1) false (coupling.push (r, x1)) allowFactor
      | none =>
        -- Both finds stalled.  If the form is already factored, give up;
        -- otherwise factor (to expose product-buried randoms) and retry.
        -- `allowFactor := false` (ablation) gives up here instead: strictly
        -- more incomplete, may report false INSECURE, never false SECURE.
        if factored || !allowFactor then (g, false, coupling)
        else
          let (dag, tuple') := g.dag.factor tuple
          rewriteComplete { g with dag } tuple' used fuel true coupling allowFactor

/-- Fuel budget for the complete loop: a generous multiple of the circuit's
    random count.  Termination is *argued* (each general step retires one random
    into `used`, ≤ #randoms of them; simple steps between them shrink the tuple)
    but not proved, so fuel is the safety net.  Exhausting it returns `false` —
    only ever a false negative, never a false SECURE. -/
def rewriteFuel (g : GlobalDAG) : Nat :=
  (g.dag.randoms.size + 2) * 256

/-- Entry point for the complete checker on a tuple of observation roots.
    Returns the coupling `T` (ordered `(r, t)` substitutions) used to certify it. -/
def checkProbeCompleteT (g : GlobalDAG) (tuple : Array NodeId)
    (allowFactor : Bool := true) : GlobalDAG × Bool × Array (NodeId × NodeId) :=
  rewriteComplete g tuple {} (rewriteFuel g) false #[] allowFactor

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
def checkProbeRoots (g : GlobalDAG) (rootIds : Array NodeId)
    (allowFactor : Bool := true) : GlobalDAG × Bool :=
  let (g, ps)       := initProbeByIds g rootIds
  let (g, ps, sec)  := rewriteLoop g ps
  if sec then (g, true)
  else if !allowFactor then
    -- Factoring disabled (ablation): skip tier 2, general loop without factoring.
    let (g, sec3, _) := checkProbeCompleteT g rootIds false
    (g, sec3)
  else
    let (dag, froots) := g.dag.factor ps.roots
    let g := { g with dag }
    let (g, ps2)      := initProbeByIds g froots
    let (g, _, sec2)  := rewriteLoop g ps2
    if sec2 then (g, true)
    else
      let (g, sec3, _) := checkProbeCompleteT g rootIds
      (g, sec3)

end verif
