import Verif.«n-aryDAG»
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Circuit and Global DAG

The netlist frontend: `WireInput`/`WireDef`/`Circuit` describe the 2-ary
wire-level circuit (probeable body wires vs. atomically-encoded input shares),
and `GlobalDAG` bridges it into the hash-consed 𝔽₂ DAG (`n-aryDAG.lean`),
registering wire → NodeId.  Nothing here knows about probing or rewriting —
see `Engine.lean` (rewrite engine) and `Coupling.lean` (extension).
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

end verif
