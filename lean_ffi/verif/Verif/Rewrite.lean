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

/-- A wire-level netlist. -/
structure Circuit where
  wireOrder : Array String           := #[]
  wireDefs  : HashMap String WireDef := {}
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

/-- Reverse dependency index: for each wire `w`, the list of wires whose
    `WireDef` references `w` as an input.  Useful for an incremental
    closure worklist algorithm. -/
def buildReverseDeps (c : Circuit) : HashMap String (Array String) :=
  c.wireDefs.fold (fun acc name d =>
    d.inputs.foldl (fun acc inp =>
      match inp with
      | WireInput.wire target =>
        let cur := (acc[target]?).getD #[]
        if cur.contains name then acc
        else acc.insert target (cur.push name)
      | _ => acc) acc)
    {}

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

def ppCircuit (c : Circuit) : String :=
  String.intercalate "\n" (c.wireOrder.toList.map fun name =>
    match c.wireDefs[name]? with
    | some d => s!"  {name} = {ppWireDef d}"
    | none   => s!"  {name} = ??")

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

-- low-level DAG access

@[inline]
def addWire (g : GlobalDAG) (name : String) (id : NodeId) : GlobalDAG :=
  { g with wires := g.wires.insert name id }

@[inline]
def wireId? (g : GlobalDAG) (name : String) : Option NodeId :=
  g.wires[name]?

def mkLeaf (g : GlobalDAG) (v : VarType) : GlobalDAG × NodeId :=
  let (d, id) := g.dag.mkLeaf v
  ({ g with dag := d }, id)

def mkXor (g : GlobalDAG) (ids : Array NodeId) : GlobalDAG × NodeId :=
  let (d, id) := g.dag.mkXor ids
  ({ g with dag := d }, id)

def mkAnd (g : GlobalDAG) (ids : Array NodeId) : GlobalDAG × NodeId :=
  let (d, id) := g.dag.mkAnd ids
  ({ g with dag := d }, id)

def mkConst (g : GlobalDAG) (b : Bool) : GlobalDAG × NodeId :=
  let (d, id) := g.dag.mkConst b
  ({ g with dag := d }, id)

@[inline]
def ppNode (g : GlobalDAG) (id : NodeId) : String :=
  g.dag.ppNode id

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
    builds the corresponding DAG node, and registers wire→NodeId. -/
def addWireXor (g : GlobalDAG) (name : String) (inputs : Array WireInput) : GlobalDAG :=
  if g.circuit.hasWire name then g
  else
    let (g, ids) := g.resolveInputs inputs
    let (dag, nid) := g.dag.mkXor ids
    { g with dag     := dag
             wires   := g.wires.insert name nid
             circuit := g.circuit.addWire name (WireDef.xor inputs) }

/-- Declare a wire `name = AND(inputs)`. -/
def addWireAnd (g : GlobalDAG) (name : String) (inputs : Array WireInput) : GlobalDAG :=
  if g.circuit.hasWire name then g
  else
    let (g, ids) := g.resolveInputs inputs
    let (dag, nid) := g.dag.mkAnd ids
    { g with dag     := dag
             wires   := g.wires.insert name nid
             circuit := g.circuit.addWire name (WireDef.and inputs) }

/-- Factor the expression of every registered wire, updating `g.wires` to
    point at the factored root NodeIds.  Idempotent in practice: rerunning
    on the same wires allocates no new DAG nodes. -/
def factorAllWires (g : GlobalDAG) : GlobalDAG :=
  g.wires.fold (fun g name oldId =>
    let (dag', newId) := g.dag.factorNode oldId
    { g with dag := dag', wires := g.wires.insert name newId })
    g

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
  xorParCount      : HashMap NodeId Nat
  totalParCount    : HashMap NodeId Nat
  mulDepth         : HashMap NodeId Nat
  parents          : HashMap NodeId (Array NodeId)
  todo             : Array NodeId
  rewrittenRandoms : HashMap NodeId Unit
  deriving Inhabited

namespace ProbeState

@[inline]
def isStandalone (ps : ProbeState) (id : NodeId) : Bool :=
  ps.totalParCount[id]? == some 1 && ps.xorParCount[id]? == some 1

@[inline]
def isRandom (ps : ProbeState) (dag : DAG) (id : NodeId) : Bool :=
  ps.rewrittenRandoms.contains id ||
  match dag.kind? id with
  | some (NodeKind.leaf (VarType.Random _)) => true
  | _                                       => false

end ProbeState

def insertTodoByDepth (ps : ProbeState) (r : NodeId) : ProbeState :=
  let d := (ps.mulDepth[r]?).getD 0
  let pos := (ps.todo.findIdx? (fun rid => (ps.mulDepth[rid]?).getD 0 > d)).getD ps.todo.size
  { ps with todo := ps.todo.insertIdx! pos r }

/-- Probe initialisation by pre-factored root NodeIds.

    Calls `factor` defensively even after `factorAllWires` has been run.
    The cost is bounded: factoring is idempotent on already-factored subgraphs
    (every `mkXor`/`mkAnd` hits an existing intern entry); however, the factor
    chosen for a XOR node can in principle change when the set of *probe
    roots* presented restricts the view of common factors. -/
def initProbeByIds (g : GlobalDAG) (rootIds : Array NodeId) : GlobalDAG × ProbeState :=
  let (dag, factoredRoots) := g.dag.factor rootIds
  let g := { g with dag := dag }
  let s : DFSState := factoredRoots.foldl (dfsRoot g.dag) {}
  let todoUnsorted := g.dag.randoms.filter (fun rId =>
    s.totalParCount[rId]? == some 1 && s.xorParCount[rId]? == some 1)
  let todo := todoUnsorted.qsort (fun a b => (s.mulDepth[a]?).getD 0 < (s.mulDepth[b]?).getD 0)
  (g, {
    roots            := factoredRoots
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
      if ps.isRandom dag nodeId && tpc' == 1 && xpc' == 1 then insertTodoByDepth ps nodeId
      else ps

def applyRewrite (g : GlobalDAG) (ps : ProbeState) (r : NodeId) : GlobalDAG × ProbeState :=
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

partial def rewriteLoop (g : GlobalDAG) (ps : ProbeState) : GlobalDAG × ProbeState × Bool :=
  if isSecure g ps then (g, ps, true)
  else
    match ps.todo[0]? with
    | none   => (g, ps, false)
    | some r =>
      let ps := { ps with todo := ps.todo.eraseIdx! 0 }
      let (g', ps') := applyRewrite g ps r
      rewriteLoop g' ps'

-- ============================================================
-- Examples
-- ============================================================

/-! ## DOM-AND circuit -/
def sharedDomAND : GlobalDAG := ({} : GlobalDAG)
  |>.addWireAnd "a0b0" #[WireInput.leaf (VarType.Secret "a0"), WireInput.leaf (VarType.Secret "b0")]
  |>.addWireAnd "a0b1" #[WireInput.leaf (VarType.Secret "a0"), WireInput.leaf (VarType.Secret "b1")]
  |>.addWireAnd "a1b0" #[WireInput.leaf (VarType.Secret "a1"), WireInput.leaf (VarType.Secret "b0")]
  |>.addWireAnd "a1b1" #[WireInput.leaf (VarType.Secret "a1"), WireInput.leaf (VarType.Secret "b1")]
  |>.addWireXor "s0"   #[WireInput.wire "a0b0", .wire "a0b1", WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "s1"   #[WireInput.wire "a1b0", .wire "a1b1", WireInput.leaf (VarType.Random "r")]

#eval IO.println (Circuit.ppCircuit sharedDomAND.circuit)

end verif
