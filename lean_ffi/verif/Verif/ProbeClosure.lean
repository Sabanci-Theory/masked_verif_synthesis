import Verif.«n-aryDAG»
import Verif.Rewrite
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Probe Enumeration with Closure-Based Extension
-/

-- ============================================================
-- Wire index (NodeId → wire names)
-- ============================================================

def buildWireIndex (fw : HashMap String NodeId) : HashMap NodeId (Array String) :=
  fw.fold (fun acc name nid =>
    let cur := (acc[nid]?).getD #[]
    acc.insert nid (cur.push name))
    {}

-- ============================================================
-- Computability helpers
-- ============================================================

/-- A WireInput is computable given the current `known` set if the adversary
    can derive its value from probes, publics, and constants. -/
def isComputable (inp : WireInput) (known : HashMap String Unit) : Bool :=
  match inp with
  | WireInput.const _                 => true
  | WireInput.leaf (VarType.Public _) => true
  | WireInput.leaf (VarType.Secret _) => false
  | WireInput.leaf (VarType.Random _) => false
  | WireInput.wire name               => known.contains name

def isWireRef (inp : WireInput) : Option String :=
  match inp with
  | WireInput.wire name => some name
  | _                   => none

/-- Symmetric difference of two WireInput arrays, treated as GF(2) multisets:
    an element survives iff its total count across both arrays is odd. -/
def symmDiff (a b : Array WireInput) : Array WireInput := Id.run do
  let mut counts : HashMap WireInput Nat := {}
  for x in a do
    counts := counts.insert x ((counts[x]?.getD 0) + 1)
  for x in b do
    counts := counts.insert x ((counts[x]?.getD 0) + 1)
  let mut result : Array WireInput := #[]
  for (k, v) in counts.toArray do
    if v % 2 == 1 then result := result.push k
  return result

-- ============================================================
-- Closure: equivalence, forward/backward, symmetric-difference containment
-- ============================================================

/-- Equivalence rule: for each known wire, add all wires sharing its NodeId. -/
def applyEquivalence
    (fw : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (known : HashMap String Unit)
    : HashMap String Unit :=
  known.fold (fun acc w _ =>
    match fw[w]? with
    | some nid => let equivs := (wireIndex[nid]?).getD #[]
                  equivs.foldl (fun a w' => a.insert w' ()) acc
    | none     => acc)
    known

/-- Forward (XOR/AND) and backward (XOR-only) propagation rules. -/
def propagateForwardBackward (circ : Circuit) (known : HashMap String Unit)
    : HashMap String Unit × Bool :=
  circ.wireOrder.foldl (fun (known, changed) name =>
    match circ.wireDefs[name]? with
    | none   => (known, changed)
    | some d =>
      let wKnown := known.contains name
      let inputs := d.inputs
      -- Forward: w not known, all inputs computable.
      if !wKnown && inputs.all (fun inp => isComputable inp known) then
        (known.insert name (), true)
      -- Backward (XOR only): w known, exactly one non-computable input,
      -- and that input is a wire reference.
      else if d.isXor && wKnown then
        let nonComp := inputs.filter (fun inp => !isComputable inp known)
        if nonComp.size != 1 then (known, changed)
        else
          match isWireRef nonComp[0]! with
          | some wname => (known.insert wname (), true)
          | none       => (known, changed)
      else (known, changed))
    (known, false)

/-- Symmetric-difference containment: for each known XOR wire `wp` and each
    candidate XOR wire `wq`, deduce `wq` if `symmDiff I_p I_q` is all
    computable. -/
def propagateContainment (circ : Circuit) (known : HashMap String Unit)
    : HashMap String Unit × Bool :=
  circ.wireOrder.foldl (fun (known, changed) wp =>
    if !known.contains wp then (known, changed)
    else
      match circ.wireDefs[wp]? with
      | some (WireDef.xor I_p) =>
        circ.wireOrder.foldl (fun (known, changed) wq =>
          if known.contains wq then (known, changed)
          else
            match circ.wireDefs[wq]? with
            | some (WireDef.xor I_q) => let D := symmDiff I_p I_q
              if D.all (fun inp => isComputable inp known) then (known.insert wq (), true)
              else (known, changed)
            | _ => (known, changed))
          (known, changed)
      | _ => (known, changed))
    (known, false)

/-- Closure under all three rules; iterates to fixpoint. -/
partial def closureWires
    (circ      : Circuit)
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (Y         : Array String)
    : Array String :=
  let initial : HashMap String Unit := Y.foldl (fun s w => s.insert w ()) {}
  let rec iter (known : HashMap String Unit) : HashMap String Unit :=
    let known := applyEquivalence fw wireIndex known
    let (known, c1) := propagateForwardBackward circ known
    let (known, c2) := propagateContainment circ known
    if c1 || c2 then iter known else known
  let final := iter initial
  final.fold (fun acc w _ => acc.push w) #[]

-- ============================================================
-- Worklist and check result
-- ============================================================

structure ProbeFactor where
  count : Nat
  wires : Array String
  deriving Repr, Inhabited

abbrev ProbeWorklist := Array ProbeFactor

inductive CheckResult
  | Secure
  | Insecure : Array String → CheckResult
  deriving Repr, Inhabited

def CheckResult.isSecure : CheckResult → Bool
  | CheckResult.Secure     => true
  | CheckResult.Insecure _ => false

@[inline]
def wireNamesToIds (fw : HashMap String NodeId) (names : Array String) : Array NodeId :=
  names.filterMap (fw[·]?)

@[inline]
def isWorklistVacuous (wl : ProbeWorklist) : Bool :=
  wl.any (fun f => f.count > 0 && f.wires.size < f.count)

@[inline]
def cleanWorklist (wl : ProbeWorklist) : ProbeWorklist :=
  wl.filter (fun f => f.count > 0)

/-- Run DFS + rewrite loop on a wire-name set, via the bridge map. -/
def checkProbeByNames (g : GlobalDAG) (fw : HashMap String NodeId) (names : Array String)
    : GlobalDAG × ProbeState × Bool :=
  let ids := wireNamesToIds fw names
  let (g, ps) := initProbeByIds g ids
  rewriteLoop g ps

-- ============================================================
-- Credit-based probe construction
-- ============================================================

partial def buildProbeSetSingle
    (circ       : Circuit)
    (fw         : HashMap String NodeId)
    (wireIndex  : HashMap NodeId (Array String))
    (credits    : Nat)
    (candidates : Array String)
    : Array String × Array String :=
  let rec loop (chosen : Array String) (left : Nat) :=
    if left == 0 then (chosen, closureWires circ fw wireIndex chosen)
    else
      let cur := closureWires circ fw wireIndex chosen
      let curSet : HashMap String Unit := cur.foldl (fun m w => m.insert w ()) {}
      let fresh := candidates.filter (fun w => !curSet.contains w)
      if fresh.isEmpty then (chosen, cur)
      else
        let best := fresh.foldl (fun best w =>
          let c' := closureWires circ fw wireIndex (chosen.push w)
          match best with
          | none          => some (w, c'.size)
          | some (_, bsz) => if c'.size > bsz then some (w, c'.size) else best)
          none
        match best with
        | some (w, _) => loop (chosen.push w) (left - 1)
        | none        => (chosen, cur)
  loop #[] credits

partial def buildProbeSetMulti
    (circ      : Circuit)
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (wl        : ProbeWorklist)
    : Array String × Array String :=
  let initRem := wl.map (·.count)
  let rec loop (chosen : Array String) (rem : Array Nat) :=
    let cur := closureWires circ fw wireIndex chosen
    let curSet : HashMap String Unit := cur.foldl (fun m w => m.insert w ()) {}
    let candidates : Array (String × Nat) := Id.run do
      let mut acc := #[]
      for idx in [:wl.size] do
        if rem[idx]! != 0 then
          for w in wl[idx]!.wires do
            if !curSet.contains w then acc := acc.push (w, idx)
      return acc
    if candidates.isEmpty then
      let chosenSet : HashMap String Unit := chosen.foldl (fun m w => m.insert w ()) {}
      let leftovers : Array (String × Nat) := Id.run do
        let mut acc := #[]
        for idx in [:wl.size] do
          if rem[idx]! != 0 then
            for w in wl[idx]!.wires do
              if !chosenSet.contains w then acc := acc.push (w, idx)
        return acc
      if leftovers.isEmpty then (chosen, cur)
      else
        let (w, idx) := leftovers[0]!
        loop (chosen.push w) (rem.set! idx (rem[idx]! - 1))
    else
      let best := candidates.foldl (fun best (w, idx) =>
        let c' := closureWires circ fw wireIndex (chosen.push w)
        match best with
        | none             => some (w, idx, c'.size)
        | some (_, _, bsz) =>
          if c'.size > bsz then some (w, idx, c'.size) else best)
        none
      match best with
      | some (w, idx, _) => loop (chosen.push w) (rem.set! idx (rem[idx]! - 1))
      | none             => (chosen, cur)
  loop #[] initRem

-- ============================================================
-- CheckAll
-- ============================================================

mutual

partial def checkAllSingle
    (g         : GlobalDAG)
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (count     : Nat)
    (wires     : Array String)
    : GlobalDAG × CheckResult :=
  if count == 0 then (g, CheckResult.Secure)
  else if wires.size < count then (g, CheckResult.Secure)
  else
    let (g, _, allSec) := checkProbeByNames g fw wires
    if allSec then (g, CheckResult.Secure)
    else
      let (chosen, closure) := buildProbeSetSingle g.circuit fw wireIndex count wires
      let (g, _, chosenSec) := checkProbeByNames g fw chosen
      if !chosenSec then (g, CheckResult.Insecure chosen)
      else
        let closureSet : HashMap String Unit := closure.foldl (fun m w => m.insert w ()) {}
        let unsafeWires := wires.filter (fun w => !closureSet.contains w)
        let (g, r1) := checkAllSingle g fw wireIndex count unsafeWires
        if !r1.isSecure then (g, r1)
        else
          let safeWithinWires := wires.filter (fun w => closureSet.contains w)
          let rec doMixed (g : GlobalDAG) (i : Nat) : GlobalDAG × CheckResult :=
            if i == 0 then (g, CheckResult.Secure)
            else
              let (g, ri) := checkAllMulti g fw wireIndex #[{ count := i, wires := safeWithinWires },
                                                            { count := count - i, wires := unsafeWires }]
              if !ri.isSecure then (g, ri)
              else doMixed g (i - 1)
          doMixed g (count - 1)

partial def checkAllMulti
    (g         : GlobalDAG)
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (wl        : ProbeWorklist)
    : GlobalDAG × CheckResult :=
  if isWorklistVacuous wl then (g, CheckResult.Secure)
  else
    let wl := cleanWorklist wl
    if wl.isEmpty then (g, CheckResult.Secure)
    else if wl.size == 1 then
      checkAllSingle g fw wireIndex wl[0]!.count wl[0]!.wires
    else
      let allWires := wl.foldl (fun acc f => acc ++ f.wires) #[]
      let (g, _, allSec) := checkProbeByNames g fw allWires
      if allSec then (g, CheckResult.Secure)
      else
        let (chosen, closure) := buildProbeSetMulti g.circuit fw wireIndex wl
        let (g, _, chosenSec) := checkProbeByNames g fw chosen
        if !chosenSec then (g, CheckResult.Insecure chosen)
        else
          let closureSet : HashMap String Unit := closure.foldl (fun m w => m.insert w ()) {}
          let unsafeWl : ProbeWorklist := wl.map (fun f =>
            { count := f.count
              wires := f.wires.filter (fun w => !closureSet.contains w) })
          let (g, r1) := checkAllMulti g fw wireIndex unsafeWl
          if !r1.isSecure then (g, r1)
          else
            let rec splitFactor (g : GlobalDAG) (jIdx : Nat) : GlobalDAG × CheckResult :=
              if jIdx >= wl.size then (g, CheckResult.Secure)
              else
                let f := wl[jIdx]!
                let safeJ   := f.wires.filter (fun w => closureSet.contains w)
                let unsafeJ := f.wires.filter (fun w => !closureSet.contains w)
                let rec doI (g : GlobalDAG) (i : Nat) : GlobalDAG × CheckResult :=
                  if i == 0 then splitFactor g (jIdx + 1)
                  else
                    let newWl : ProbeWorklist := (wl.extract 0 jIdx)
                      ++ #[{ count := i, wires := safeJ }, { count := f.count - i, wires := unsafeJ }]
                      ++ (wl.extract (jIdx + 1) wl.size)
                    let (g, ri) := checkAllMulti g fw wireIndex newWl
                    if !ri.isSecure then (g, ri)
                    else doI g (i - 1)
                doI g (f.count - 1)
            splitFactor g 0

end

-- ============================================================
-- Public entry point
-- ============================================================

def checkDProbing (g : GlobalDAG) (probingOrder : Nat) : GlobalDAG × HashMap String NodeId × CheckResult :=
  let g := g.factorAllWires
  let fw := g.wires
  let wireIndex := buildWireIndex fw
  let allWires := g.circuit.wireOrder
  let (g, res) := checkAllSingle g fw wireIndex probingOrder allWires
  (g, fw, res)

def ppResult (res : CheckResult) (order : Nat) : String :=
  match res with
  | CheckResult.Secure =>
    s!"SECURE at order {order}: all probe sets certified."
  | CheckResult.Insecure names =>
    let label := "{" ++ String.intercalate ", " names.toList ++ "}"
    s!"INSECURE at order {order}: counterexample {label}"

-- ============================================================
-- Examples
-- ============================================================

/-! ## Example 1 — first-order masked wire, secure at order 1 -/
def circuit1 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]

#eval do
  let (g, _, res) := checkDProbing circuit1 1
  IO.println "=== Example 1 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 1)

/-! ## Example 2 — XOR linear closure between wires (backward rule)

    w1 = a + r1,  w2 = b + r2,  w3 = w1 + w2

    Probing w3 alone is secure (uniform via r1, r2). At order 2, probing
    {w1, w3} unlocks w2 via XOR backward at w3's def — `propagateForwardBackward`
    sees w3 known, all leaf inputs computable (there are none), exactly one
    non-computable wire-input (w2), so w2 enters known. -/
def circuit2 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r1")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r2")]
  |>.addWireXor "w3" #[WireInput.wire "w1", WireInput.wire "w2"]

#eval do
  let (_, _, res1) := checkDProbing circuit2 1
  let (g, _, res2) := checkDProbing circuit2 2
  IO.println "=== Example 2 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println (ppResult res2 2)

/-! ## Example 3 — DOM-AND -/
def domAND : GlobalDAG := ({} : GlobalDAG)
  -- Share production for a and b.
  |>.addWireXor "a0" #[WireInput.leaf (VarType.Random "r_a")]
  |>.addWireXor "a1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r_a")]
  |>.addWireXor "b0" #[WireInput.leaf (VarType.Random "r_b")]
  |>.addWireXor "b1" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r_b")]
  -- DOM-AND gadget.
  |>.addWireAnd "a0b0" #[WireInput.wire "a0", WireInput.wire "b0"]
  |>.addWireAnd "a0b1" #[WireInput.wire "a0", WireInput.wire "b1"]
  |>.addWireAnd "a1b0" #[WireInput.wire "a1", WireInput.wire "b0"]
  |>.addWireAnd "a1b1" #[WireInput.wire "a1", WireInput.wire "b1"]
  |>.addWireXor "s0"   #[WireInput.wire "a0b0", WireInput.wire "a0b1", WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "s1"   #[WireInput.wire "a1b0", WireInput.wire "a1b1", WireInput.leaf (VarType.Random "r")]

#eval do
  let (_, _, res1) := checkDProbing domAND 1
  let (g, _, res2) := checkDProbing domAND 2
  IO.println "=== Example 3 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println (ppResult res2 2)

/-! ## Example 4

    Two wires whose factored expressions canonicalise to the same NodeId.
    The equivalence rule fires immediately on the second wire when the first
    is in known. -/
def circuit4 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]

#eval do
  let (g, _, res) := checkDProbing circuit4 1
  IO.println "=== Example 4 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 1)

/-! ## Example 5 — symmetric-difference containment

    w1 = a + r + b   (b is a Public leaf, hence computable)
    w2 = a + r

    The WireDef inputs differ by `{leaf (Public "b")}`.  Since b is
    computable, the symm-diff rule deduces w2 ∈ cl({w1}).  At order 1,
    probing w1 alone certifies both w1 and w2 in a single rewrite call.

    Note: this only works because w1 and w2 are both directly defined XOR
    gates whose inputs can be matched as multisets.  If w1 instead referenced
    an intermediate wire u = a + r, then `propagateForwardBackward` would
    deduce u first (via XOR backward on w1) and the equivalence rule on
    (u, w2) would catch the rest. -/
def circuit5 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r"),
                       WireInput.leaf (VarType.Public "b")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]

#eval do
  let (g, _, res) := checkDProbing circuit5 1
  IO.println "=== Example 5 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 1)

end verif
