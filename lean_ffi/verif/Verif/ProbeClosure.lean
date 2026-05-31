import Verif.«n-aryDAG»
import Verif.Rewrite
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Probe Enumeration with Closure-Based Extension
-/

-- ============================================================
-- Wire index and helpers
-- ============================================================

def buildWireIndex (fw : HashMap String NodeId) : HashMap NodeId (Array String) :=
  fw.fold (fun acc name nid =>
    let cur := (acc[nid]?).getD #[]
    acc.insert nid (cur.push name))
    {}

private def isComputable (inp : WireInput) (known : HashMap String Unit) : Bool :=
  match inp with
  | .const _          => true
  | .leaf (.Public _) => true
  | .leaf (.Secret _) => false
  | .leaf (.Random _) => false
  | .wire name        => known.contains name

private def isWireRef (inp : WireInput) : Option String :=
  match inp with
  | .wire name => some name
  | _          => none

/-- Symmetric difference as a GF(2) multiset: an element survives iff its
    total count is odd. -/
private def symmDiff (a b : Array WireInput) : Array WireInput := Id.run do
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
-- Per-rule deductions on a single wire
-- ============================================================

/-- Try the forward/backward rules on wire `name`.  Returns the wire(s) to
    newly add to known, if any. -/
private def tryForwardBackward
    (circ : Circuit) (known : HashMap String Unit) (name : String)
    : Option String :=
  match circ.wireDefs[name]? with
  | none   => none
  | some d =>
    let wKnown := known.contains name
    let inputs := d.inputs
    if !wKnown && inputs.all (fun inp => isComputable inp known) then
      some name
    else if d.isXor && wKnown then
      let nonComp := inputs.filter (fun inp => !isComputable inp known)
      if nonComp.size != 1 then none
      else isWireRef nonComp[0]!
    else none

/-- Try the symm-diff rule with `wp` as source and `wq` as candidate. -/
private def trySymmDiff
    (circ : Circuit) (known : HashMap String Unit) (wp wq : String) : Bool :=
  if known.contains wq then false
  else match circ.wireDefs[wp]?, circ.wireDefs[wq]? with
  | some (WireDef.xor I_p), some (WireDef.xor I_q) =>
    let D := symmDiff I_p I_q
    D.all (fun inp => isComputable inp known)
  | _, _ => false

-- ============================================================
-- Equivalence rule
-- ============================================================

def applyEquivalence
    (fw : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (known : HashMap String Unit)
    : HashMap String Unit × Bool :=
  let known' := known.fold (fun acc w _ =>
    match fw[w]? with
    | some nid =>
      let equivs := (wireIndex[nid]?).getD #[]
      equivs.foldl (fun a w' => a.insert w' ()) acc
    | none => acc) known
  (known', known'.size > known.size)

-- ============================================================
-- Worklist-driven propagation
-- ============================================================

/-- Drain a worklist of newly-known wires, applying forward/backward and
    symm-diff (with the newly-known wire as source) until the worklist is
    empty.  Updates `known` in place. -/
private partial def drainWorklist
    (circ      : Circuit)
    (revDeps   : HashMap String (Array String))
    (known     : HashMap String Unit)
    (worklist  : Array String)
    : HashMap String Unit :=
  if worklist.size = 0 then known
  else
    let w := worklist[worklist.size - 1]!
    let rest := worklist.pop
    -- Forward/backward: re-examine every wire that references `w`.
    let dependents := (revDeps[w]?).getD #[]
    let (known, rest) := dependents.foldl (fun (k, wl) u =>
      match tryForwardBackward circ k u with
      | some newName =>
        if k.contains newName then (k, wl)
        else (k.insert newName (), wl.push newName)
      | none => (k, wl)) (known, rest)
    -- Forward/backward, on w itself: if w just became known, its own
    -- WireDef's backward rule may newly fire.  Already covered above via
    -- revDeps lookups; w itself does not depend on w.
    -- Symm-diff with w as source (only if w is an XOR wire).
    let (known, rest) := match circ.wireDefs[w]? with
      | some (WireDef.xor _) =>
        circ.wireOrder.foldl (fun (k, wl) wq =>
          if k.contains wq then (k, wl)
          else if trySymmDiff circ k w wq then
            (k.insert wq (), wl.push wq)
          else (k, wl)) (known, rest)
      | _ => (known, rest)
    drainWorklist circ revDeps known rest

/-- A coarse fallback pass: re-scan `circ.wireOrder` once for forward/backward
    and once for symm-diff.  Returns the new known set, list of newly-added
    wires (to seed the next worklist), and whether anything changed.

    This catches the case where a wire `w` newly became known and is now in
    the differing part of some other pair's symm-diff that wasn't directly
    indexed.  Run at most once per closure call after the worklist drains. -/
private def coarsePass
    (circ : Circuit) (known : HashMap String Unit)
    : HashMap String Unit × Array String × Bool :=
  -- Forward/backward over all wires.
  let (known, added1) := circ.wireOrder.foldl (fun (k, ad) name =>
    match tryForwardBackward circ k name with
    | some newName =>
      if k.contains newName then (k, ad)
      else (k.insert newName (), ad.push newName)
    | none => (k, ad)) (known, #[])
  -- Symm-diff over all known-XOR × candidate-XOR pairs.
  let (known, added2) := circ.wireOrder.foldl (fun (k, ad) wp =>
    if !k.contains wp then (k, ad)
    else match circ.wireDefs[wp]? with
      | some (WireDef.xor _) =>
        circ.wireOrder.foldl (fun (k, ad) wq =>
          if k.contains wq then (k, ad)
          else if trySymmDiff circ k wp wq then
            (k.insert wq (), ad.push wq)
          else (k, ad)) (k, ad)
      | _ => (k, ad)) (known, added1)
  let changed := added2.size > 0
  (known, added2, changed)

-- ============================================================
-- Top-level closure
-- ============================================================

/-- Compute the closure of `Y` under equivalence, forward/backward, and
    symm-diff containment.  Uses an incremental worklist driven by the
    reverse-dependency index. -/
partial def closureWires
    (circ      : Circuit)
    (revDeps   : HashMap String (Array String))
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (Y         : Array String)
    : Array String :=
  let initial : HashMap String Unit :=
    Y.foldl (fun s w => s.insert w ()) {}
  let rec iter (known : HashMap String Unit) (seed : Array String)
      : HashMap String Unit :=
    -- Equivalence first.
    let (known, eqChanged) := applyEquivalence fw wireIndex known
    -- Build the worklist from the seed plus any equivalence-added wires
    -- (for simplicity we just dump `known` if equivalence changed).
    let wl : Array String :=
      if eqChanged then known.fold (fun acc w _ => acc.push w) #[]
      else seed
    let known := drainWorklist circ revDeps known wl
    -- Coarse fallback to catch missed symm-diff candidacies.
    let (known, addedCoarse, changedCoarse) := coarsePass circ known
    if changedCoarse then iter known addedCoarse else known
  let final := iter initial Y
  final.fold (fun acc w _ => acc.push w) #[]

/-
partial def closureWires
    (circ      : Circuit)
    (revDeps   : HashMap String (Array String))
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (Y         : Array String)
    : Array String :=
  Y
-/

-- ============================================================
-- Worklist and check result (unchanged)
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

def checkProbeByNames (g : GlobalDAG) (fw : HashMap String NodeId)
    (names : Array String) : GlobalDAG × ProbeState × Bool :=
  let ids := wireNamesToIds fw names
  let (g, ps) := initProbeByIds g ids
  rewriteLoop g ps

-- ============================================================
-- Probe construction — now takes revDeps, otherwise unchanged
-- ============================================================

partial def buildProbeSetSingle
    (circ       : Circuit)
    (revDeps    : HashMap String (Array String))
    (fw         : HashMap String NodeId)
    (wireIndex  : HashMap NodeId (Array String))
    (credits    : Nat)
    (candidates : Array String)
    : Array String × Array String :=
  let rec loop (chosen : Array String) (left : Nat) :=
    if left == 0 then (chosen, closureWires circ revDeps fw wireIndex chosen)
    else
      let cur := closureWires circ revDeps fw wireIndex chosen
      let curSet : HashMap String Unit :=
        cur.foldl (fun m w => m.insert w ()) {}
      let fresh := candidates.filter (fun w => !curSet.contains w)
      if fresh.isEmpty then (chosen, cur)
      else
        let best := fresh.foldl (fun best w =>
          let c' := closureWires circ revDeps fw wireIndex (chosen.push w)
          match best with
          | none           => some (w, c'.size)
          | some (_, bsz) => if c'.size > bsz then some (w, c'.size) else best)
          none
        match best with
        | some (w, _) => loop (chosen.push w) (left - 1)
        | none        => (chosen, cur)
  loop #[] credits

partial def buildProbeSetMulti
    (circ      : Circuit)
    (revDeps   : HashMap String (Array String))
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (wl        : ProbeWorklist)
    : Array String × Array String :=
  let initRem := wl.map (·.count)
  let rec loop (chosen : Array String) (rem : Array Nat) :=
    let cur := closureWires circ revDeps fw wireIndex chosen
    let curSet : HashMap String Unit :=
      cur.foldl (fun m w => m.insert w ()) {}
    let candidates : Array (String × Nat) := Id.run do
      let mut acc := #[]
      for idx in [:wl.size] do
        if rem[idx]! != 0 then
          for w in wl[idx]!.wires do
            if !curSet.contains w then acc := acc.push (w, idx)
      return acc
    if candidates.isEmpty then
      let chosenSet : HashMap String Unit :=
        chosen.foldl (fun m w => m.insert w ()) {}
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
        let c' := closureWires circ revDeps fw wireIndex (chosen.push w)
        match best with
        | none                => some (w, idx, c'.size)
        | some (_, _, bsz)    =>
          if c'.size > bsz then some (w, idx, c'.size) else best)
        none
      match best with
      | some (w, idx, _) => loop (chosen.push w) (rem.set! idx (rem[idx]! - 1))
      | none             => (chosen, cur)
  loop #[] initRem

-- ============================================================
-- CheckAll — now threads revDeps
-- ============================================================

mutual

partial def checkAllSingle
    (g         : GlobalDAG)
    (revDeps   : HashMap String (Array String))
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (count     : Nat)
    (wires     : Array String)
    : GlobalDAG × CheckResult :=
  if count == 0 then (g, .Secure)
  else if wires.size < count then (g, .Secure)
  else
    let (g, _, allSec) := checkProbeByNames g fw wires
    if allSec then (g, CheckResult.Secure)
    else
      let (chosen, closure) :=
        buildProbeSetSingle g.circuit revDeps fw wireIndex count wires
      let (g, _, chosenSec) := checkProbeByNames g fw chosen
      if !chosenSec then (g, CheckResult.Insecure chosen)
      else
        let closureSet : HashMap String Unit :=
          closure.foldl (fun m w => m.insert w ()) {}
        let unsafeWires := wires.filter (fun w => !closureSet.contains w)
        let (g, r1) := checkAllSingle g revDeps fw wireIndex count unsafeWires
        if !r1.isSecure then (g, r1)
        else
          let safeWithinWires := wires.filter (fun w => closureSet.contains w)
          let rec doMixed (g : GlobalDAG) (i : Nat) : GlobalDAG × CheckResult :=
            if i == 0 then (g, .Secure)
            else
              let (g, ri) := checkAllMulti g revDeps fw wireIndex
                #[{ count := i,         wires := safeWithinWires },
                  { count := count - i, wires := unsafeWires }]
              if !ri.isSecure then (g, ri)
              else doMixed g (i - 1)
          doMixed g (count - 1)

partial def checkAllMulti
    (g         : GlobalDAG)
    (revDeps   : HashMap String (Array String))
    (fw        : HashMap String NodeId)
    (wireIndex : HashMap NodeId (Array String))
    (wl        : ProbeWorklist)
    : GlobalDAG × CheckResult :=
  if isWorklistVacuous wl then (g, .Secure)
  else
    let wl := cleanWorklist wl
    if wl.isEmpty then (g, CheckResult.Secure)
    else if wl.size == 1 then
      checkAllSingle g revDeps fw wireIndex wl[0]!.count wl[0]!.wires
    else
      let allWires := wl.foldl (fun acc f => acc ++ f.wires) #[]
      let (g, _, allSec) := checkProbeByNames g fw allWires
      if allSec then (g, CheckResult.Secure)
      else
        let (chosen, closure) :=
          buildProbeSetMulti g.circuit revDeps fw wireIndex wl
        let (g, _, chosenSec) := checkProbeByNames g fw chosen
        if !chosenSec then (g, CheckResult.Insecure chosen)
        else
          let closureSet : HashMap String Unit :=
            closure.foldl (fun m w => m.insert w ()) {}
          let unsafeWl : ProbeWorklist := wl.map (fun f =>
            { count := f.count
              wires := f.wires.filter (fun w => !closureSet.contains w) })
          let (g, r1) := checkAllMulti g revDeps fw wireIndex unsafeWl
          if !r1.isSecure then (g, r1)
          else
            let rec splitFactor (g : GlobalDAG) (jIdx : Nat)
                : GlobalDAG × CheckResult :=
              if jIdx >= wl.size then (g, .Secure)
              else
                let f := wl[jIdx]!
                let safeJ   := f.wires.filter (fun w => closureSet.contains w)
                let unsafeJ := f.wires.filter (fun w => !closureSet.contains w)
                let rec doI (g : GlobalDAG) (i : Nat) : GlobalDAG × CheckResult :=
                  if i == 0 then splitFactor g (jIdx + 1)
                  else
                    let newWl : ProbeWorklist :=
                      (wl.extract 0 jIdx)
                        ++ #[{ count := i,           wires := safeJ },
                             { count := f.count - i, wires := unsafeJ }]
                        ++ (wl.extract (jIdx + 1) wl.size)
                    let (g, ri) := checkAllMulti g revDeps fw wireIndex newWl
                    if !ri.isSecure then (g, ri)
                    else doI g (i - 1)
                doI g (f.count - 1)
            splitFactor g 0

end

-- ============================================================
-- Public entry point — builds revDeps once
-- ============================================================

def checkDProbing (g : GlobalDAG) (probingOrder : Nat)
    : GlobalDAG × HashMap String NodeId × CheckResult :=
  let g := g.factorAllWires
  let fw := g.wires
  let wireIndex := buildWireIndex fw
  let revDeps := g.circuit.buildReverseDeps
  let allWires := g.circuit.wireOrder
  let (g, res) := checkAllSingle g revDeps fw wireIndex probingOrder allWires
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

/-! ## Example 6 — Q⁴₁₂ quadratic bijection -/
def circuitF : GlobalDAG := ({} : GlobalDAG)
  -- share production
  |>.addWireXor "a1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r0")]
  |>.addWireXor "a2" #[WireInput.leaf (VarType.Random "r0")]
  |>.addWireXor "b1" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r1")]
  |>.addWireXor "b2" #[WireInput.leaf (VarType.Random "r1")]
  |>.addWireXor "c1" #[WireInput.leaf (VarType.Secret "c"), WireInput.leaf (VarType.Random "r2")]
  |>.addWireXor "c2" #[WireInput.leaf (VarType.Random "r2")]
  |>.addWireXor "d1" #[WireInput.leaf (VarType.Secret "d"), WireInput.leaf (VarType.Random "r3")]
  |>.addWireXor "d2" #[WireInput.leaf (VarType.Random "r3")]
  -- product gates
  |>.addWireAnd "a1c1" #[WireInput.wire "a1", WireInput.wire "c1"]
  |>.addWireAnd "a1c2" #[WireInput.wire "a1", WireInput.wire "c2"]
  |>.addWireAnd "a2c1" #[WireInput.wire "a2", WireInput.wire "c1"]
  |>.addWireAnd "a2c2" #[WireInput.wire "a2", WireInput.wire "c2"]
  |>.addWireAnd "a1b1" #[WireInput.wire "a1", WireInput.wire "b1"]
  |>.addWireAnd "a1b2" #[WireInput.wire "a1", WireInput.wire "b2"]
  |>.addWireAnd "a2b1" #[WireInput.wire "a2", WireInput.wire "b1"]
  |>.addWireAnd "a2b2" #[WireInput.wire "a2", WireInput.wire "b2"]
  -- outputs
  |>.addWireXor "x1" #[WireInput.wire "a1"]
  |>.addWireXor "x2" #[WireInput.wire "a2"]
  |>.addWireXor "y1" #[WireInput.wire "a1c1", WireInput.wire "b1"]
  |>.addWireXor "y2" #[WireInput.wire "a1c2"]
  |>.addWireXor "y3" #[WireInput.wire "a2c1", WireInput.wire "b2"]
  |>.addWireXor "y4" #[WireInput.wire "a2c2"]
  |>.addWireXor "z1" #[WireInput.wire "a1b1", WireInput.wire "a1c1", WireInput.wire "c1"]
  |>.addWireXor "z2" #[WireInput.wire "a1b2", WireInput.wire "a1c2"]
  |>.addWireXor "z3" #[WireInput.wire "a2b1", WireInput.wire "a2c1"]
  |>.addWireXor "z4" #[WireInput.wire "a2b2", WireInput.wire "a2c2", WireInput.wire "c2"]
  |>.addWireXor "t1" #[WireInput.wire "d1"]
  |>.addWireXor "t2" #[WireInput.wire "d2"]
  -- Recombination layer.
  |>.addWireXor "xb1" #[WireInput.wire "x1"]
  |>.addWireXor "xb2" #[WireInput.wire "x2"]
  |>.addWireXor "yb1" #[WireInput.wire "y1", WireInput.wire "y2"]
  |>.addWireXor "yb2" #[WireInput.wire "y3", WireInput.wire "y4"]
  |>.addWireXor "zb1" #[WireInput.wire "z1", WireInput.wire "z2"]
  |>.addWireXor "zb2" #[WireInput.wire "z3", WireInput.wire "z4"]
  |>.addWireXor "tb1" #[WireInput.wire "t1"]
  |>.addWireXor "tb2" #[WireInput.wire "t2"]

#eval do
  let (g, _, res1) := checkDProbing circuitF 1
  IO.println "=== F: shared Q⁴₁₂ (no extra r) ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  let (_, _, res2) := checkDProbing circuitF 2
  IO.println (ppResult res2 2)

/-! ### Example 7 — DOM-AND with 3 shares -/
def circuitG : GlobalDAG := ({} : GlobalDAG)
  -- share production for a
  |>.addWireXor "a0" #[.leaf (.Random "ra0")]
  |>.addWireXor "a1" #[.leaf (.Random "ra1")]
  |>.addWireXor "a2" #[.leaf (.Secret "a"), .leaf (.Random "ra0"), .leaf (.Random "ra1")]
  -- share production for b
  |>.addWireXor "b0" #[.leaf (.Random "rb0")]
  |>.addWireXor "b1" #[.leaf (.Random "rb1")]
  |>.addWireXor "b2" #[.leaf (.Secret "b"), .leaf (.Random "rb0"), .leaf (.Random "rb1")]
  -- diagonal products
  |>.addWireAnd "u0" #[.wire "a0", .wire "b0"]
  |>.addWireAnd "u1" #[.wire "a1", .wire "b1"]
  |>.addWireAnd "u2" #[.wire "a2", .wire "b2"]
  -- cross products
  |>.addWireAnd "p01" #[.wire "a0", .wire "b1"]
  |>.addWireAnd "p10" #[.wire "a1", .wire "b0"]
  |>.addWireAnd "p02" #[.wire "a0", .wire "b2"]
  |>.addWireAnd "p20" #[.wire "a2", .wire "b0"]
  |>.addWireAnd "p12" #[.wire "a1", .wire "b2"]
  |>.addWireAnd "p21" #[.wire "a2", .wire "b1"]
  -- masked cross terms
  |>.addWireXor "c01" #[.wire "p01", .leaf (.Random "r01")]
  |>.addWireXor "c10" #[.wire "p10", .leaf (.Random "r01")]
  |>.addWireXor "c02" #[.wire "p02", .leaf (.Random "r02")]
  |>.addWireXor "c20" #[.wire "p20", .leaf (.Random "r02")]
  |>.addWireXor "c12" #[.wire "p12", .leaf (.Random "r12")]
  |>.addWireXor "c21" #[.wire "p21", .leaf (.Random "r12")]
  -- outputs
  |>.addWireXor "s0" #[.wire "u0", .wire "c01", .wire "c02"]
  |>.addWireXor "s1" #[.wire "u1", .wire "c10", .wire "c12"]
  |>.addWireXor "s2" #[.wire "u2", .wire "c20", .wire "c21"]

#eval do
  let (g, _, res1) := checkDProbing circuitG 1
  let (_, _, res2) := checkDProbing circuitG 2
  let (_, _, res3) := checkDProbing circuitG 3
  IO.println "=== G: 3-share DOM-AND ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println (ppResult res2 2)
  IO.println (ppResult res3 3)

end verif
