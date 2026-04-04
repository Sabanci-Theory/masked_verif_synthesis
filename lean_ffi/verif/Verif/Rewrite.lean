import Verif.«n-aryDAG»
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Global DAG, Probe State, and Rewritable Random Detection
-/

-- ============================================================
-- Global DAG
-- ============================================================

/-- The global DAG representing a circuit.
    `dag`   — hash-consed nodes.
    `wires` — maps wire name → `NodeId`. -/
structure GlobalDAG where
  dag   : DAG                   := {}
  wires : HashMap String NodeId := {}

namespace GlobalDAG

/-- Registers `id` as the root of wire `name`. -/
@[inline]
def addWire (gdag : GlobalDAG) (name : String) (id : NodeId) : GlobalDAG :=
  { gdag with wires := gdag.wires.insert name id }

/-- Looks up a wire's `NodeId`. -/
@[inline]
def wireId? (gdag : GlobalDAG) (name : String) : Option NodeId :=
  gdag.wires[name]?

def mkLeaf (gdag : GlobalDAG) (v : VarType) : GlobalDAG × NodeId :=
  let (d, id) := gdag.dag.mkLeaf v
  ({ gdag with dag := d }, id)

def mkXor (gdag : GlobalDAG) (ids : Array NodeId) : GlobalDAG × NodeId :=
  let (d, id) := gdag.dag.mkXor ids
  ({ gdag with dag := d }, id)

def mkAnd (gdag : GlobalDAG) (ids : Array NodeId) : GlobalDAG × NodeId :=
  let (d, id) := gdag.dag.mkAnd ids
  ({ gdag with dag := d }, id)

def mkConst (gdag : GlobalDAG) (b : Bool) : GlobalDAG × NodeId :=
  let (d, id) := gdag.dag.mkConst b
  ({ gdag with dag := d }, id)

def ppNode (gdag : GlobalDAG) (id : NodeId) : String :=
  gdag.dag.ppNode id

end GlobalDAG

-- ============================================================
-- DFS for parent tracking
-- ============================================================

/-!
### DFS

The DFS worker visits each node's children at most once (`visited`).

`totalParCount[n]` equals the number of distinct nodes in the
probe context that directly reference `n`, which is the "fan-in".
-/

/-- Accumulated state during the DFS. -/
structure DFSState where
  xorParCount   : HashMap NodeId Nat            := {}
  totalParCount : HashMap NodeId Nat            := {}
  mulDepth      : HashMap NodeId Nat            := {}
  parents       : HashMap NodeId (Array NodeId) := {}
  visited       : HashMap NodeId Unit           := {}

/-- Processes one edge `parent → childId`. -/
partial def dfsChild (dag : DAG) (s : DFSState) (childId : NodeId) (parentId : NodeId)
  (childDepth : Nat) (parentIsXor : Bool)
  : DFSState :=
  -- Record this parent edge.
  let tpc  := (s.totalParCount[childId]?).getD 0 + 1
  let xpc  := (s.xorParCount[childId]?).getD 0 + (if parentIsXor then 1 else 0)
  let d    := min childDepth ((s.mulDepth[childId]?).getD (childDepth + 1))
  let pars := ((s.parents[childId]?).getD #[]).push parentId
  let s := { s with
    totalParCount := s.totalParCount.insert childId tpc
    xorParCount   := s.xorParCount.insert   childId xpc
    mulDepth      := s.mulDepth.insert      childId d
    parents       := s.parents.insert       childId pars }
  -- Recurse only if this is the first visit.
  if s.visited.contains childId then s
  else
    let s := { s with visited := s.visited.insert childId () }
    match dag.kind? childId with
    | some (NodeKind.xorNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid childId d true) s
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid childId (d + 1) false) s
    | _ => s -- leaf or const: no children

/-- Starts a DFS from a probe root. -/
partial def dfsRoot (dag : DAG) (s : DFSState) (rootId : NodeId) : DFSState :=
  if s.visited.contains rootId then s
  else
    let s := { s with
      visited  := s.visited.insert rootId ()
      mulDepth := s.mulDepth.insert rootId 0 }
    match dag.kind? rootId with
    | some (NodeKind.xorNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid rootId 0 true) s
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid rootId 1 false) s
    | _ => s

-- ============================================================
-- Probe State
-- ============================================================

/-- Per-probe analysis state.
    ```
    n ∈ todo ↔ n ∈ dag.randoms
             ∧ totalParCount[n] = 1
             ∧ xorParCount[n] = 1
    ```

    Only `roots`, the two count maps, and `todo` are allocated per probe.
    The underlying `DAG` is shared with the `GlobalDAG` and is not deep-copied. -/
structure ProbeState where
  roots            : Array NodeId
  /-- Number of XOR-node parents per reachable node. -/
  xorParCount      : HashMap NodeId Nat
  /-- Total parent count per reachable node. -/
  totalParCount    : HashMap NodeId Nat
  /-- Minimum multiplicative depth of a node. -/
  mulDepth         : HashMap NodeId Nat
  /-- Parents of a node. -/
  parents          : HashMap NodeId (Array NodeId)
  /-- Rewritable random leaves. -/
  todo             : Array NodeId
  /-- XOR nodes that have been rewritten as fresh randoms. -/
  rewrittenRandoms : HashMap NodeId Unit
  /-- Record of rewritten randoms, in order. -/
  rewriteHistory   : Array (NodeId × Array NodeId)

namespace ProbeState

/-- Checks if `NodeId` is rewritable. -/
@[inline]
def isStandalone (ps : ProbeState) (id : NodeId) : Bool :=
  ps.totalParCount[id]? == some 1 && ps.xorParCount[id]? == some 1

@[inline]
def isRandom (ps : ProbeState) (dag : DAG) (id : NodeId) : Bool :=
  ps.rewrittenRandoms.contains id ||
  match dag.kind? id with
  | some (NodeKind.leaf (VarType.Random _)) => true
  | _                                       => false

/-- Pretty-printing for debugging. -/
def pp (ps : ProbeState) (dag : DAG) : String :=
  let ppIds ids := String.intercalate ", " (ids.toList.map dag.ppNode)
  s!"  Roots              : [{ppIds ps.roots}]\n" ++
  s!"  Rewritable randoms : [{ppIds ps.todo}]"

end ProbeState

-- ============================================================
-- Probe initialization
-- ============================================================

/-- Inserts `r` into `ps.todo` at the position that maintains ascending
    `mulDepth` order. -/
def insertTodoByDepth (ps : ProbeState) (r : NodeId) : ProbeState :=
  let d := (ps.mulDepth[r]?).getD 0
  -- Find the first existing entry whose depth exceeds d.
  let pos := (ps.todo.findIdx? (fun rid => (ps.mulDepth[rid]?).getD 0 > d)).getD
    ps.todo.size -- no random exceeds d
  { ps with todo := ps.todo.insertIdx! pos r }

/-- Initializes a probe context for the given wire names.

    ## The pipeline is as follows

    **Step 1) Resolve**: map each wire name to its root `NodeId` via
    `gdag.wires`. (returns an error for any unknown wire name)

    **Step 2) Factor**: run `DAG.factor` on each probe root. This may
    intern new factored nodes into `gdag.dag`. Factoring precedes the DFS
    because it restructures expressions, potentially revealing standalone
    randoms that were previously hidden inside AND products.

    **Step 3) DFS**: one pass over the reachable subgraph to compute
    `xorParCount` and `totalParCount`.

    **Step 4) Filter**: scan `dag.randoms` and filter those with
    `totalParCount = xorParCount = 1`.

    Note: Factoring may extend the DAG with new factored nodes. The subsequent
    probes must use the returned `GlobalDAG` so that those new nodes are visible
    and can be hash-cons'ed again. -/
def initProbe (gdag : GlobalDAG) (wireNames : Array String)
  : Except String (GlobalDAG × ProbeState) := do
  -- Step 1: resolve wire names → NodeIds.
  let origRoots ← wireNames.mapM fun name =>
    match gdag.wireId? name with
    | some id => Except.ok id
    | none    => Except.error s!"Unknown wire: '{name}'"
  -- Step 2: factor each root, passing the dag along.
  let (dag, factoredRoots) := gdag.dag.factor origRoots
  let gdag := { gdag with dag := dag }
  -- Step 3: DFS from all factored roots.
  let s : DFSState := factoredRoots.foldl (dfsRoot gdag.dag) {}
  -- Step 4: collect standalone randoms from the global randoms array.
  let todoUnsorted := gdag.dag.randoms.filter fun rId => -- Q: we filter all the randoms
                            -- but we can just filter the randoms encountered during DFS
    s.totalParCount[rId]? == some 1 && s.xorParCount[rId]?   == some 1
  let todo := todoUnsorted.qsort (fun a b =>
    (s.mulDepth[a]?).getD 0 < (s.mulDepth[b]?).getD 0)
  return (gdag, {
    roots            := factoredRoots
    xorParCount      := s.xorParCount
    totalParCount    := s.totalParCount
    mulDepth         := s.mulDepth
    parents          := s.parents
    todo             := todo
    rewrittenRandoms := {}
    rewriteHistory   := #[]
  })

/-- Same as above but probes by `NodeId` directly. -/
def initProbeByIds (gdag : GlobalDAG) (rootIds : Array NodeId)
  : GlobalDAG × ProbeState :=
  let (dag, factoredRoots) := gdag.dag.factor rootIds
  let gdag := { gdag with dag := dag }
  let s : DFSState := factoredRoots.foldl (dfsRoot gdag.dag) {}
  let todoUnsorted := gdag.dag.randoms.filter fun rId =>
    s.totalParCount[rId]? == some 1 &&
    s.xorParCount[rId]?   == some 1
  let todo := todoUnsorted.qsort (fun a b =>
    (s.mulDepth[a]?).getD 0 < (s.mulDepth[b]?).getD 0)
  (gdag, {
    roots            := factoredRoots
    xorParCount      := s.xorParCount
    totalParCount    := s.totalParCount
    mulDepth         := s.mulDepth
    parents          := s.parents
    todo             := todo
    rewrittenRandoms := {}
    rewriteHistory   := #[]
  })

-- ============================================================
-- Check
-- ============================================================

/-- Considers the probe secure iff:
    (i) no probe root is itself a secret leaf, and
    (ii) no secret leaf has a non-zero parent count (reachability). -/
def isSecure (gdag : GlobalDAG) (ps : ProbeState) : Bool :=
  ps.roots.all (fun rid => !(gdag.dag.isSecretNode rid)) &&
  gdag.dag.secrets.all (fun sid => (ps.totalParCount[sid]?).getD 0 == 0)

-- ============================================================
-- Parent count update
-- ============================================================

/-- Decrements the parent count of `nodeId` by one (the parent `wasXor`
    indicates whether the lost edge was through an XOR gate).
    If the count reaches zero, cascades to the node's children. -/
partial def decrementParent (dag : DAG) (ps : ProbeState) (nodeId : NodeId) (wasXor : Bool)
  : ProbeState :=
  let tpc := (ps.totalParCount[nodeId]?).getD 0
  if tpc == 0 then ps  -- already unreachable, so nothing to do. Q: is this code reachable?
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
      -- Remove from todo if present
      let ps := { ps with todo := ps.todo.filter (· != nodeId) } -- Q: (!)
      if ps.rewrittenRandoms.contains nodeId then ps
      else -- Cascade through DAG children unless this node was already rewritten
        match dag.kind? nodeId with
        | some (NodeKind.xorNode ch) =>
          ch.foldl (fun acc cid =>
            let ps' := { acc with parents :=
                         acc.parents.insert cid (((acc.parents[cid]?).getD #[]).filter (· != nodeId)) }
            decrementParent dag ps' cid true) ps
        | some (NodeKind.andNode ch) =>
          ch.foldl (fun acc cid =>
            let ps' := { acc with parents :=
                         acc.parents.insert cid (((acc.parents[cid]?).getD #[]).filter (· != nodeId)) }
            decrementParent dag ps' cid false) ps
        | _ => ps  -- leaf, so nothing to cascade
    else
      -- The node still reachable.  Check if it just became a standalone random.
      if ps.isRandom dag nodeId && tpc' == 1 && xpc' == 1 then
        insertTodoByDepth ps nodeId
      else ps

-- ============================================================
-- The rewrite
-- ============================================================

/-!
## One rewrite step

Given standalone random `r` with unique XOR parent `x`:

1. Add `x` to `rewrittenRandoms` (x now acts as a fresh random leaf).
2. Remove `r` from all tracking structures (it has been absorbed into x).
3. For each sibling `c_i ≠ r` of `r` inside `x`:
   - Remove `x` from `parents[c_i]`.
   - Decrement `c_i`'s count (with cascade if it hits zero).
4. If `x` itself is now standalone (inherited x's original parents, and
   those counts are (1,1)), enqueue `x` for a future rewrite.
-/

def applyRewrite (gdag : GlobalDAG) (ps : ProbeState) (r : NodeId)
  : GlobalDAG × ProbeState :=
  let x := ((ps.parents[r]?).getD #[])[0]!   -- sole XOR parent of `r`
  -- Get x's children from the DAG.
  let xCh := match gdag.dag.kind? x with
    | some (NodeKind.xorNode ch) => ch
    | _                          => #[]
  -- Step 1: mark `x` as a rewritten random.
  let siblings := xCh.filter (· != r)
  let ps := { ps with
    rewrittenRandoms := ps.rewrittenRandoms.insert x ()
    rewriteHistory   := ps.rewriteHistory.push (r, siblings)
    -- Step 2: remove r from all tracking.
    totalParCount := ps.totalParCount.erase r
    xorParCount   := ps.xorParCount.erase   r
    mulDepth      := ps.mulDepth.erase      r
    parents       := ps.parents.erase       r }
  -- Step 3: disconnect `x` from each sibling `c_i ≠ r` and cascade.
  let ps := siblings.foldl (fun ps ci =>
    -- Remove `x` from `c_i`'s parent list.
    let newPars := ((ps.parents[ci]?).getD #[]).filter (· != x)
    let ps := { ps with parents := ps.parents.insert ci newPars }
    -- Decrement `c_i`'s count.
    decrementParent gdag.dag ps ci true) ps
  (gdag, ps)

-- ============================================================
-- Rewrite loop
-- ============================================================

/-- Repeatedly applies rewrites until the probe is secure or no further rewrites
    are possible.

    The loop processes `todo` entries from the front (minimum multiplicative
    depth first). `findIdx?` skips stale entries whose `isStandalone`
    condition is no longer satisfied. -/
partial def rewriteLoop (gdag : GlobalDAG) (ps : ProbeState)
  : GlobalDAG × ProbeState × Bool :=
  if isSecure gdag ps then (gdag, ps, true)
  else
    match ps.todo[0]? with
    | none   => (gdag, ps, false)   -- no more rewrites available
    | some r =>
      -- Remove the consumed entry before rewriting.
      let ps := { ps with todo := ps.todo.eraseIdx! 0 }
      let (gdag', ps') := applyRewrite gdag ps r
      rewriteLoop gdag' ps'

/-- Full probe pipeline: init + rewrite loop.
    Returns `(updatedGlobalDAG, finalProbeState, probeIsSecure)`. -/
def checkProbe (gdag : GlobalDAG) (wireNames : Array String)
    : Except String (GlobalDAG × ProbeState × Bool) := do
  let (gdag', ps) ← initProbe gdag wireNames
  return rewriteLoop gdag' ps

-- ============================================================
-- Witness production
-- ============================================================

/-- Deep copies a node, priming variables and substituting randoms based on `W`. -/
partial def substPrime (dag : DAG) (W : HashMap NodeId NodeId) (memo : HashMap NodeId NodeId) (id : NodeId)
  : DAG × HashMap NodeId NodeId × NodeId :=
  if let some res := memo[id]? then (dag, memo, res)
  else match dag.kind? id with
    | some (NodeKind.leaf (VarType.Random _)) =>
      -- If the random has a computed witness in W, use it.
      -- Otherwise, it's an unrewritten random, so it just maps to itself (r' = r).
      let res := (W[id]?).getD id
      (dag, memo.insert id res, res)

    | some (NodeKind.leaf v) =>
      let v' := match v with
        | VarType.Secret s => VarType.Secret (s ++ "'")
        | VarType.Public p => VarType.Public (p ++ "'")
        | _                => v
      let (dag', res) := dag.mkLeaf v'
      (dag', memo.insert id res, res)

    | some (NodeKind.constVal b) =>
      let (dag', res) := dag.mkConst b
      (dag', memo.insert id res, res)

    | some (NodeKind.xorNode ch) =>
      let (dag', memo', ch') := ch.foldl (fun (d, m, acc) cid =>
        let (d', m', cid') := substPrime d W m cid
        (d', m', acc.push cid')) (dag, memo, #[])
      let (dag'', res) := dag'.mkXor ch'
      (dag'', memo'.insert id res, res)

    | some (NodeKind.andNode ch) =>
      let (dag', memo', ch') := ch.foldl (fun (d, m, acc) cid =>
        let (d', m', cid') := substPrime d W m cid
        (d', m', acc.push cid')) (dag, memo, #[])
      let (dag'', res) := dag'.mkAnd ch'
      (dag'', memo'.insert id res, res)

    | none => (dag, memo, id)

/-- Generates the witness coupling function for a secure probe.
    Returns the updated DAG and a map from original random NodeId to its witness NodeId. -/
def buildWitness (gdag : GlobalDAG) (ps : ProbeState) : GlobalDAG × HashMap NodeId NodeId :=
  -- Fold over the history in reverse chronological order
  let (dagFinal, WFinal) := ps.rewriteHistory.reverse.foldl (fun (dag, W) (r, siblings) =>
    -- 1. e = XOR of the siblings
    let (dag1, e_id) := dag.mkXor siblings
    -- 2. e' = primed version of E (substituting known witnesses)
    -- We use a fresh memo for each rewrite step to ensure W updates take effect.
    let (dag2, _, e_prime_id) := substPrime dag1 W {} e_id
    -- 3. r' = e' + e + r
    let (dag3, witness_id) := dag2.mkXor #[e_prime_id, e_id, r]
    -- Store the computed witness for this random
    (dag3, W.insert r witness_id)) (gdag.dag, {})
  ({ gdag with dag := dagFinal }, WFinal)

-- ============================================================
-- Witness Formatting
-- ============================================================

/-- Formats the witness map into a readable multiline string. -/
def ppWitness (gdag : GlobalDAG) (W : HashMap NodeId NodeId) : String :=
  if W.isEmpty then "  Witness: None generated (no rewrites applied)"
  else
    let lines := W.toList.map fun (origId, witId) =>
      s!"    {gdag.dag.ppNode origId}' := {gdag.dag.ppNode witId}"
    "  Witness:\n" ++ String.intercalate "\n" lines

-- ============================================================
-- Examples
-- ============================================================

/-! ## Example 1 — r0 is rewritable when probing one wire but not two

    Circuit:
      w1 = e * a + r0
      w2 = e * b + r0
-/
def circuit1 : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, e)  := g.mkLeaf (VarType.Public "e")
  let (g, a)  := g.mkLeaf (VarType.Secret "a")
  let (g, b)  := g.mkLeaf (VarType.Secret "b")
  let (g, r0) := g.mkLeaf (VarType.Random "r0")
  let (g, ea) := g.mkAnd  #[e, a]
  let (g, eb) := g.mkAnd  #[e, b]
  let (g, w1) := g.mkXor  #[ea, r0]
  let (g, w2) := g.mkXor  #[eb, r0]
  (g.addWire "w1" w1).addWire "w2" w2

def example1 : IO Unit := do
  let g := circuit1
  for probe in [#["w1"], #["w2"], #["w1", "w2"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match checkProbe g probe with
    | Except.error e          => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps, sec) =>
        IO.println s!"Probe {label}: secure = {sec}\n{ps.pp g'.dag}"
        if sec then
          let (g'', W) := buildWitness g' ps
          IO.println (ppWitness g'' W)

#eval example1

/-! ## Example 2 — factoring

    Circuit:
      w = e * a + e * b + r0
-/
def circuit2 : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, e)  := g.mkLeaf (VarType.Public "e")
  let (g, a)  := g.mkLeaf (VarType.Secret "a")
  let (g, b)  := g.mkLeaf (VarType.Secret "b")
  let (g, r0) := g.mkLeaf (VarType.Random "r0")
  let (g, ea) := g.mkAnd #[e, a]
  let (g, eb) := g.mkAnd #[e, b]
  let (g, w)  := g.mkXor #[ea, eb, r0]
  g.addWire "w" w

def example2 : IO Unit := do
  let g := circuit2
  let origRoot := (g.wireId? "w").get!
  IO.println s!"Original: {g.ppNode origRoot}"
  match checkProbe g #["w"] with
  | Except.error e          => IO.println s!"Error: {e}"
  | Except.ok (g', ps, sec) =>
      IO.println s!"Probe w: secure = {sec}\n{ps.pp g'.dag}"
      if sec then
        let (g'', W) := buildWitness g' ps
        IO.println (ppWitness g'' W)

#eval example2

/-! ## Example 3 — 2 share DOM-AND gate

    s0 = a0*b0 + a0*b1 + r,  s1 = a1*b0 + a1*b1 + r
-/
def domAND : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a0) := g.mkLeaf (VarType.Secret "a0")
  let (g, a1) := g.mkLeaf (VarType.Secret "a1")
  let (g, b0) := g.mkLeaf (VarType.Secret "b0")
  let (g, b1) := g.mkLeaf (VarType.Secret "b1")
  let (g, r)  := g.mkLeaf (VarType.Random "r")
  let (g, a0b0) := g.mkAnd #[a0, b0]
  let (g, a0b1) := g.mkAnd #[a0, b1]
  let (g, a1b0) := g.mkAnd #[a1, b0]
  let (g, a1b1) := g.mkAnd #[a1, b1]
  let (g, s0)   := g.mkXor #[a0b0, a0b1, r]
  let (g, s1)   := g.mkXor #[a1b0, a1b1, r]
  (g.addWire "w0" s0).addWire "w1" s1

def example3 : IO Unit := do
  let g := domAND
  for probe in [#["w0"], #["w1"], #["w0", "w1"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match initProbe g probe with
    | Except.error e     => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps) => IO.println s!"Probe {label}:\n{ps.pp g'.dag}"

def example3_rewrite : IO Unit := do
  let g := domAND
  for probe in [#["w0"], #["w1"], #["w0", "w1"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match checkProbe g probe with
    | Except.error e          => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps, sec) =>
        IO.println s!"Probe {label}: secure = {sec}\n{ps.pp g'.dag}"
        if sec then
          let (g'', W) := buildWitness g' ps
          IO.println (ppWitness g'' W)

#eval example3
#eval example3_rewrite

/-! ## Example 4 — flattening does not harm probing

    Circuit:
      w1 = a + r0
      w3 = w1 + r0
      w4 = w3 + r1
-/
def circuit4 : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a)  := g.mkLeaf (VarType.Secret "a")
  let (g, r0) := g.mkLeaf (VarType.Random "r0")
  let (g, r1) := g.mkLeaf (VarType.Random "r1")
  let (g, w1) := g.mkXor #[a, r0]
  let (g, w3) := g.mkXor #[w1, r0]
  let (g, w4) := g.mkXor #[w3, r1]
  ((g.addWire "w1" w1).addWire "w3" w3).addWire "w4" w4

def example4 : IO Unit := do
  let g := circuit4
  for probe in [#["w1"], #["w3"], #["w4"], #["w3", "w4"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match checkProbe g probe with
    | Except.error e          => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps, sec) =>
        IO.println s!"Probe {label}: secure = {sec}\n{ps.pp g'.dag}"
        if sec then
          let (g'', W) := buildWitness g' ps
          IO.println (ppWitness g'' W)

#eval example4

/-! ## Example 5 — Q_12^4

    s0 = (a + r0)*(b + r1) + (a + r0)*(c + r2) + (c + r2) + (a + r0)*(r1) + (a + r0)*(r2)
-/
def circuit5 : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a) := g.mkLeaf (VarType.Secret "a")
  let (g, b) := g.mkLeaf (VarType.Secret "b")
  let (g, c) := g.mkLeaf (VarType.Secret "c")
  let (g, r0) := g.mkLeaf (VarType.Random "r0")
  let (g, r1) := g.mkLeaf (VarType.Random "r1")
  let (g, r2) := g.mkLeaf (VarType.Random "r2")
  let (g, ar0) := g.mkXor #[a, r0]
  let (g, br1) := g.mkXor #[b, r1]
  let (g, cr2) := g.mkXor #[c, r2]
  let (g, t1) := g.mkAnd #[ar0, br1]
  let (g, t2) := g.mkAnd #[ar0, cr2]
  let (g, t3) := g.mkAnd #[ar0, r1]
  let (g, t4) := g.mkAnd #[ar0, r2]
  let (g, root) := g.mkXor #[t1, t2, cr2, t3, t4]
  g.addWire "w0" root

def example5 : IO Unit := do
  let g := circuit5
  let origRoot := (g.wireId? "w0").get!
  IO.println s!"Original: {g.ppNode origRoot}"
  match checkProbe g #["w0"] with
  | Except.error e          => IO.println s!"Error: {e}"
  | Except.ok (g', ps, sec) =>
      IO.println s!"Probe: secure = {sec}\n{ps.pp g'.dag}"
      if sec then
        let (g'', W) := buildWitness g' ps
        IO.println (ppWitness g'' W)

#eval example5

/-! ## Example 6

    w1 = r0 + r1 + a
    w2 = r1 + r2 + b
-/
def circuit6 : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a)  := g.mkLeaf (VarType.Secret "a")
  let (g, b)  := g.mkLeaf (VarType.Secret "b")
  let (g, r0) := g.mkLeaf (VarType.Random "r0")
  let (g, r1) := g.mkLeaf (VarType.Random "r1")
  let (g, r2) := g.mkLeaf (VarType.Random "r2")
  let (g, w0) := g.mkXor #[r0, r1, a]
  let (g, w1) := g.mkXor #[r1, r2, b]
  (g.addWire "w0" w0).addWire "w1" w1

def example6 : IO Unit := do
  let g := circuit6
  for probe in [#["w0"], #["w1"], #["w0", "w1"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match checkProbe g probe with
    | Except.error e          => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps, sec) =>
        IO.println s!"Probe {label}: secure = {sec}\n{ps.pp g'.dag}"
        if sec then
          let (g'', W) := buildWitness g' ps
          IO.println (ppWitness g'' W)

#eval example6

end verif
