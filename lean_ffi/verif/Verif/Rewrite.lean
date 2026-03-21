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
private structure DFSState where
  xorParCount   : HashMap NodeId Nat  := {}
  totalParCount : HashMap NodeId Nat  := {}
  visited       : HashMap NodeId Unit := {}

/-- Processes one edge `parent → childId`. -/
partial def dfsChild (dag : DAG) (s : DFSState) (childId : NodeId) (parentIsXor : Bool) : DFSState :=
  -- Record this parent edge.
  let tpc := s.totalParCount.insert childId ((s.totalParCount[childId]?).getD 0 + 1)
  let xpc := if parentIsXor
             then s.xorParCount.insert childId ((s.xorParCount[childId]?).getD 0 + 1)
             else s.xorParCount
  let s := { s with totalParCount := tpc, xorParCount := xpc }
  -- Recurse only if this is the first visit.
  if s.visited.contains childId then s
  else
    let s := { s with visited := s.visited.insert childId () }
    match dag.kind? childId with
    | some (NodeKind.xorNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid true)  s
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid false) s
    | _ => s  -- leaf or const: no children

/-- Starts a DFS from a probe root. -/
partial def dfsRoot (dag : DAG) (s : DFSState) (rootId : NodeId) : DFSState :=
  if s.visited.contains rootId then s
  else
    let s := { s with visited := s.visited.insert rootId () }
    match dag.kind? rootId with
    | some (NodeKind.xorNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid true)  s
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun acc cid => dfsChild dag acc cid false) s
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
  roots         : Array NodeId
  /-- Number of XOR-node parents per reachable node. -/
  xorParCount   : HashMap NodeId Nat
  /-- Total parent count per reachable node. -/
  totalParCount : HashMap NodeId Nat
  /-- Rewritable random leaves. -/
  todo          : Array NodeId

namespace ProbeState

/-- Checks if `NodeId` is rewritable. -/
@[inline]
def isStandalone (ps : ProbeState) (id : NodeId) : Bool :=
  ps.totalParCount[id]? == some 1 && ps.xorParCount[id]?   == some 1

/-- Pretty-printing for debugging. -/
def pp (ps : ProbeState) (dag : DAG) : String :=
  let ppIds ids := String.intercalate ", " (ids.toList.map dag.ppNode)
  s!"  Roots              : [{ppIds ps.roots}]\n" ++
  s!"  Rewritable randoms : [{ppIds ps.todo}]"

end ProbeState

-- ============================================================
-- Probe initialization
-- ============================================================

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
  let (dag, factoredRoots) :=
    origRoots.foldl
      (fun (d, roots) id =>
        let (d', id') := d.factor id
        (d', roots.push id'))
      (gdag.dag, #[])
  let gdag := { gdag with dag := dag }
  -- Step 3: DFS from all factored roots.
  let s : DFSState :=
    factoredRoots.foldl (dfsRoot gdag.dag) {}
  -- Step 4: collect standalone randoms from the global randoms array.
  let todo := gdag.dag.randoms.filter fun rId =>
    s.totalParCount[rId]? == some 1 &&
    s.xorParCount[rId]?   == some 1
  return (gdag, {
    roots         := factoredRoots
    xorParCount   := s.xorParCount
    totalParCount := s.totalParCount
    todo          := todo
  })

/-- Same as above but probes by `NodeId` directly. -/
def initProbeByIds (gdag : GlobalDAG) (rootIds : Array NodeId)
  : GlobalDAG × ProbeState :=
  let (dag, factoredRoots) :=
    rootIds.foldl
      (fun (d, roots) id =>
        let (d', id') := d.factor id
        (d', roots.push id'))
      (gdag.dag, #[])
  let gdag := { gdag with dag := dag }
  let s : DFSState := factoredRoots.foldl (dfsRoot gdag.dag) {}
  let todo := gdag.dag.randoms.filter fun rId =>
    s.totalParCount[rId]? == some 1 &&
    s.xorParCount[rId]?   == some 1
  (gdag, {
    roots         := factoredRoots
    xorParCount   := s.xorParCount
    totalParCount := s.totalParCount
    todo          := todo
  })

-- ============================================================
-- Examples
-- ============================================================

/-! ## Example 2 — r0 is rewritable when probing one wire but not two

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

def example2 : IO Unit := do
  let g := circuit1
  for probe in [#["w1"], #["w2"], #["w1", "w2"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match initProbe g probe with
    | Except.error e     => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps) => IO.println s!"Probe {label}:\n{ps.pp g'.dag}"

#eval example2

/-! ## Example 3 — factoring

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

def example3 : IO Unit := do
  let g := circuit2
  let origRoot := (g.wireId? "w").get!
  IO.println s!"Original w : {g.ppNode origRoot}"
  match initProbe g #["w"] with
  | Except.error e     => IO.println s!"Error: {e}"
  | Except.ok (g', ps) => IO.println s!"Probe:\n{ps.pp g'.dag}"

#eval example3

/-! ## Example 4 — 2 share DOM-AND gate

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

def example4 : IO Unit := do
  let g := domAND
  for probe in [#["w0"], #["w1"], #["w0", "w1"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match initProbe g probe with
    | Except.error e     => IO.println s!"Probe {label}: error — {e}"
    | Except.ok (g', ps) => IO.println s!"Probe {label}:\n{ps.pp g'.dag}"

#eval example4

/-! ## Example 5 — flattening does not harm probing

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

def example5 : IO Unit := do
  let g := circuit4
  for probe in [#["w1"], #["w3"], #["w4"], #["w3", "w4"]] do
    let label := "{" ++ String.intercalate ", " probe.toList ++ "}"
    match initProbe g probe with
    | .error e     => IO.println s!"Probe {label}: error — {e}"
    | .ok (g', ps) => IO.println s!"Probe {label}:\n{ps.pp g'.dag}"

#eval example5

end verif
