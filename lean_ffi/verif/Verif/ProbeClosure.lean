import Verif.«n-aryDAG»
import Verif.Rewrite
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Probe Enumeration with Topological-Greedy Closure
-/

-- ============================================================
-- Computability and topology
-- ============================================================

@[inline]
def isComputable (inp : WireInput) (known : HashMap String Unit) : Bool :=
  match inp with
  | .const _          => true
  | .leaf (.Public _) => true
  | .leaf (.Secret _) => false
  | .leaf (.Random _) => false
  | .wire name        => known.contains name

@[inline]
def isWireRef (inp : WireInput) : Option String :=
  match inp with
  | .wire name => some name
  | _          => none

structure Topology where
  /-- `consumers[w]` = wires whose `WireDef` references `w`. -/
  consumers : HashMap String (Array String)
  /-- `wireIndex[nid]` = wires whose factored expression has NodeId `nid`. -/
  wireIndex : HashMap NodeId (Array String)
  deriving Inhabited

def Topology.build (circ : Circuit) (fw : HashMap String NodeId) : Topology :=
  let consumers := circ.wireDefs.fold (fun acc name d =>
    d.inputs.foldl (fun acc inp =>
      match inp with
      | .wire target =>
        let cur := (acc[target]?).getD #[]
        if cur.contains name then acc
        else acc.insert target (cur.push name)
      | _ => acc) acc)
    {}
  let wireIndex := fw.fold (fun acc name nid =>
    let cur := (acc[nid]?).getD #[]
    acc.insert nid (cur.push name)) {}
  { consumers, wireIndex }

-- ============================================================
-- Rule firing
-- ============================================================

/-- Forward and backward rules at wire `name`. -/
@[inline]
def tryRule (circ : Circuit) (known : HashMap String Unit) (name : String)
    : Option String :=
  match circ.wireDefs[name]? with
  | none   => none
  | some d =>
    if !known.contains name && d.inputs.all (fun i => isComputable i known) then
      some name
    else if d.isXor && known.contains name then
      let nonComp := d.inputs.filter (fun i => !isComputable i known)
      if nonComp.size == 1 then isWireRef nonComp[0]! else none
    else none

/-- Add `w` to known and worklist if not already present. -/
@[inline]
def pushIfNew (known : HashMap String Unit) (wl : Array String) (w : String)
    : HashMap String Unit × Array String :=
  if known.contains w then (known, wl)
  else (known.insert w (), wl.push w)

-- ============================================================
-- Closure drain (FIFO worklist)
-- ============================================================

/-- Drain the worklist forward from `pos`.  Returns updated state. -/
partial def drainWorklist
    (circ : Circuit) (topo : Topology) (fw : HashMap String NodeId)
    (known : HashMap String Unit) (worklist : Array String) (pos : Nat)
    : HashMap String Unit × Array String :=
  if pos >= worklist.size then (known, worklist)
  else
    let w := worklist[pos]!
    -- Equivalence: NodeId siblings.
    let (known, worklist) := match fw[w]? with
      | some nid =>
        let equivs := (topo.wireIndex[nid]?).getD #[]
        equivs.foldl (fun (k, wl) w' => pushIfNew k wl w') (known, worklist)
      | none => (known, worklist)
    -- Forward / backward at consumers of w.
    let cs := (topo.consumers[w]?).getD #[]
    let (known, worklist) := cs.foldl (fun (k, wl) u =>
      match tryRule circ k u with
      | some name => pushIfNew k wl name
      | none      => (k, wl)) (known, worklist)
    -- Backward at w itself.
    let (known, worklist) := match tryRule circ known w with
      | some name => pushIfNew known worklist name
      | none      => (known, worklist)
    drainWorklist circ topo fw known worklist (pos + 1)

/-- Closure of a seed set under all three rules. -/
def closureWires
    (circ : Circuit) (topo : Topology) (fw : HashMap String NodeId)
    (Y : Array String) : Array String :=
  let (known, wl) := Y.foldl
    (fun (k, wl) w => pushIfNew k wl w) ({}, #[])
  (drainWorklist circ topo fw known wl 0).2

-- ============================================================
-- Stats
-- ============================================================

structure Stats where
  totalDischarges : Nat := 0
  successMain     : Nat := 0
  freeWiresSum    : Nat := 0
  deriving Repr, Inhabited

namespace Stats

@[inline] def addDischarge (s : Stats) : Stats :=
  { s with totalDischarges := s.totalDischarges + 1 }

@[inline] def addSuccess (s : Stats) (free : Nat) : Stats :=
  { s with successMain  := s.successMain + 1
           freeWiresSum := s.freeWiresSum + free }

def avgFreeWires (s : Stats) : Float :=
  if s.successMain == 0 then 0.0
  else Float.ofNat s.freeWiresSum / Float.ofNat s.successMain

def pp (s : Stats) : String :=
  s!"  total discharges       : {s.totalDischarges}\n  successful main probes : {s.successMain}\n  free wires (sum)       : {s.freeWiresSum}\n  free wires (avg/main)  : {s.avgFreeWires}"

end Stats

-- ============================================================
-- Worklist, check result, discharge
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

/-- Discharge a probe to the rewrite engine.  Always bumps `totalDischarges`.

    Fast path: the reference-counted simple rule (`rewriteLoop`).  If it cannot
    certify the probe, fall back to the complete optimistic-sampling checker
    (`checkProbeComplete`, simple + general rule) before declaring it insecure —
    so genuinely-secure tuples that need a linear dependency (e.g. high-order
    DOM-AND) are not reported as false counterexamples. -/
def checkProbeByNames (g : GlobalDAG) (fw : HashMap String NodeId)
    (stats : Stats) (names : Array String)
    : GlobalDAG × ProbeState × Bool × Stats :=
  let ids := wireNamesToIds fw names
  let (g, ps) := initProbeByIds g ids
  let (g, ps, sec) := rewriteLoop g ps
  if sec then (g, ps, true, stats.addDischarge)
  else
    let (g, sec2) := checkProbeComplete g ps.roots
    (g, ps, sec2, stats.addDischarge)

-- ============================================================
-- Topological-greedy probe construction
-- ============================================================

/-- Map each wire mentioned in `wl` to its factor index. -/
def wireToFactorMap (wl : ProbeWorklist) : HashMap String Nat := Id.run do
  let mut m : HashMap String Nat := {}
  for idx in [:wl.size] do
    for w in wl[idx]!.wires do
      m := m.insert w idx
  return m

/-- Sibling-spend: a wire whose acquisition would complete a consumer gate
    (all other inputs already computable), provided it belongs to a factor
    with remaining budget. -/
def findSiblingSpend
    (circ : Circuit) (topo : Topology)
    (wireToFactor : HashMap String Nat) (rem : Array Nat)
    (known : HashMap String Unit) (worklist : Array String)
    : Option (String × Nat) := Id.run do
  for w in worklist do
    let cs := (topo.consumers[w]?).getD #[]
    for u in cs do
      if known.contains u then continue
      match circ.wireDefs[u]? with
      | none => ()
      | some d =>
        let nonComp := d.inputs.filter (fun i => !isComputable i known)
        if nonComp.size == 1 then
          match isWireRef nonComp[0]! with
          | some wname =>
            if !known.contains wname then
              match wireToFactor[wname]? with
              | some idx => if rem[idx]! > 0 then return some (wname, idx)
              | none => ()
          | none => ()
  return none

/-- Pick the next credit to spend, by priority:
    sibling-spend > fresh wire > leftover. -/
def pickNext
    (circ : Circuit) (topo : Topology) (wl : ProbeWorklist)
    (wireToFactor : HashMap String Nat) (rem : Array Nat)
    (chosen : Array String) (known : HashMap String Unit)
    (worklist : Array String)
    : Option (String × Nat) := Id.run do
  -- Priority 1: sibling-spend.
  match findSiblingSpend circ topo wireToFactor rem known worklist with
  | some hit => return some hit
  | none => ()
  -- Priority 2: any fresh wire from a `rem>0` factor.
  for idx in [:wl.size] do
    if rem[idx]! > 0 then
      for w in wl[idx]!.wires do
        if !known.contains w then return some (w, idx)
  -- Priority 3: leftover from a `rem>0` factor.
  let chosenSet : HashMap String Unit :=
    chosen.foldl (fun m w => m.insert w ()) {}
  for idx in [:wl.size] do
    if rem[idx]! > 0 then
      for w in wl[idx]!.wires do
        if !chosenSet.contains w then return some (w, idx)
  return none

/-- Build a probe set respecting per-factor count constraints.  Returns
    `(chosen, closure)` where `closure` includes `chosen` plus everything
    deducible from it (the free wires). -/
partial def buildProbeTopological
    (circ : Circuit) (topo : Topology) (fw : HashMap String NodeId)
    (wl : ProbeWorklist) : Array String × Array String :=
  let wireToFactor := wireToFactorMap wl
  let initRem := wl.map (·.count)
  let rec spend
      (chosen : Array String) (rem : Array Nat)
      (known : HashMap String Unit) (worklist : Array String) (pos : Nat)
      : Array String × Array String :=
    -- Bring closure up to date before deciding.
    let (known, worklist) := drainWorklist circ topo fw known worklist pos
    if rem.all (· == 0) then (chosen, worklist)
    else match pickNext circ topo wl wireToFactor rem chosen known worklist with
      | none => (chosen, worklist)
      | some (w, idx) =>
        let chosen' := chosen.push w
        let rem'    := rem.set! idx (rem[idx]! - 1)
        let (known', worklist') := pushIfNew known worklist w
        -- Resume drain from the old end (where the new wire sits, if added).
        spend chosen' rem' known' worklist' worklist.size
  spend #[] initRem {} #[] 0

-- ============================================================
-- CheckAll: same recursion structure, threaded with Stats
-- ============================================================

mutual

partial def checkAllSingle
    (g : GlobalDAG) (topo : Topology) (fw : HashMap String NodeId)
    (stats : Stats) (count : Nat) (wires : Array String)
    : GlobalDAG × Stats × CheckResult :=
  if count == 0 then (g, stats, .Secure)
  else if wires.size < count then (g, stats, .Secure)
  else
    -- OptSampling union discharge.
    let (g, _, allSec, stats) := checkProbeByNames g fw stats wires
    if allSec then (g, stats, .Secure)
    else
      let (chosen, closure) :=
        buildProbeTopological g.circuit topo fw #[{ count, wires }]
      let (g, _, chosenSec, stats) := checkProbeByNames g fw stats chosen
      if !chosenSec then (g, stats, .Insecure chosen)
      else
        let free  := closure.size - chosen.size
        let stats := stats.addSuccess free
        let closureSet : HashMap String Unit :=
          closure.foldl (fun m w => m.insert w ()) {}
        let unsafeWires := wires.filter (fun w => !closureSet.contains w)
        let (g, stats, r1) := checkAllSingle g topo fw stats count unsafeWires
        if !r1.isSecure then (g, stats, r1)
        else
          let safeWithinWires := wires.filter (fun w => closureSet.contains w)
          let rec doMixed (g : GlobalDAG) (stats : Stats) (i : Nat)
              : GlobalDAG × Stats × CheckResult :=
            if i == 0 then (g, stats, .Secure)
            else
              let (g, stats, ri) := checkAllMulti g topo fw stats
                #[{ count := i,         wires := safeWithinWires },
                  { count := count - i, wires := unsafeWires }]
              if !ri.isSecure then (g, stats, ri)
              else doMixed g stats (i - 1)
          doMixed g stats (count - 1)

partial def checkAllMulti
    (g : GlobalDAG) (topo : Topology) (fw : HashMap String NodeId)
    (stats : Stats) (wl : ProbeWorklist)
    : GlobalDAG × Stats × CheckResult :=
  if isWorklistVacuous wl then (g, stats, .Secure)
  else
    let wl := cleanWorklist wl
    if wl.isEmpty then (g, stats, .Secure)
    else if wl.size == 1 then
      checkAllSingle g topo fw stats wl[0]!.count wl[0]!.wires
    else
      let allWires := wl.foldl (fun acc f => acc ++ f.wires) #[]
      let (g, _, allSec, stats) := checkProbeByNames g fw stats allWires
      if allSec then (g, stats, .Secure)
      else
        let (chosen, closure) := buildProbeTopological g.circuit topo fw wl
        let (g, _, chosenSec, stats) := checkProbeByNames g fw stats chosen
        if !chosenSec then (g, stats, .Insecure chosen)
        else
          let free  := closure.size - chosen.size
          let stats := stats.addSuccess free
          let closureSet : HashMap String Unit :=
            closure.foldl (fun m w => m.insert w ()) {}
          let unsafeWl : ProbeWorklist := wl.map (fun f =>
            { count := f.count
              wires := f.wires.filter (fun w => !closureSet.contains w) })
          let (g, stats, r1) := checkAllMulti g topo fw stats unsafeWl
          if !r1.isSecure then (g, stats, r1)
          else
            let rec splitFactor (g : GlobalDAG) (stats : Stats) (jIdx : Nat)
                : GlobalDAG × Stats × CheckResult :=
              if jIdx >= wl.size then (g, stats, .Secure)
              else
                let f := wl[jIdx]!
                let safeJ   := f.wires.filter (fun w => closureSet.contains w)
                let unsafeJ := f.wires.filter (fun w => !closureSet.contains w)
                let rec doI (g : GlobalDAG) (stats : Stats) (i : Nat)
                    : GlobalDAG × Stats × CheckResult :=
                  if i == 0 then splitFactor g stats (jIdx + 1)
                  else
                    let newWl : ProbeWorklist :=
                      (wl.extract 0 jIdx)
                        ++ #[{ count := i,           wires := safeJ },
                             { count := f.count - i, wires := unsafeJ }]
                        ++ (wl.extract (jIdx + 1) wl.size)
                    let (g, stats, ri) := checkAllMulti g topo fw stats newWl
                    if !ri.isSecure then (g, stats, ri)
                    else doI g stats (i - 1)
                doI g stats (f.count - 1)
            splitFactor g stats 0

end

-- ============================================================
-- Public entry point
-- ============================================================

def checkDProbing (g : GlobalDAG) (probingOrder : Nat)
    : GlobalDAG × HashMap String NodeId × CheckResult × Stats :=
  let fw := g.wires
  let topo := Topology.build g.circuit fw
  let allWires := g.circuit.wireOrder
  let (g, stats, res) := checkAllSingle g topo fw {} probingOrder allWires
  (g, fw, res, stats)

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
  let (g, _, res, stats) := checkDProbing circuit1 1
  IO.println "=== Example 1 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 1)
  IO.println stats.pp

/-! ## Example 2 — XOR linear closure between wires (backward rule)

    w1 = a + r1,  w2 = b + r2,  w3 = w1 + w2

    Probing w3 alone is secure (uniform via r1, r2). At order 2, probing
    {w1, w3} unlocks w2 via the XOR backward rule at w3's def — `tryRule`
    (driven by `drainWorklist`) sees w3 known, all leaf inputs computable
    (there are none), exactly one non-computable wire-input (w2), so w2
    enters known. -/
def circuit2 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r1")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r2")]
  |>.addWireXor "w3" #[WireInput.wire "w1", WireInput.wire "w2"]

#eval do
  let (_, _, res1, stats1) := checkDProbing circuit2 1
  let (g, _, res2, stats2) := checkDProbing circuit2 2
  IO.println "=== Example 2 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println stats1.pp
  IO.println (ppResult res2 2)
  IO.println stats2.pp

/-! ## Example 3 — DOM-AND -/
def domAND : GlobalDAG := ({} : GlobalDAG)
  -- Input shares of a and b (atomically encoded; not probe targets).
  |>.addShare "a0" #[WireInput.leaf (VarType.Random "r_a")]
  |>.addShare "a1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r_a")]
  |>.addShare "b0" #[WireInput.leaf (VarType.Random "r_b")]
  |>.addShare "b1" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r_b")]
  -- DOM-AND gadget (2-ary: cross terms a0b1 / a1b0 are masked by r first).
  |>.addWireAnd "a0b0" #[WireInput.wire "a0", WireInput.wire "b0"]
  |>.addWireAnd "a0b1" #[WireInput.wire "a0", WireInput.wire "b1"]
  |>.addWireAnd "a1b0" #[WireInput.wire "a1", WireInput.wire "b0"]
  |>.addWireAnd "a1b1" #[WireInput.wire "a1", WireInput.wire "b1"]
  |>.addWireXor "m0"   #[WireInput.wire "a0b1", WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "m1"   #[WireInput.wire "a1b0", WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "s0"   #[WireInput.wire "a0b0", WireInput.wire "m0"]
  |>.addWireXor "s1"   #[WireInput.wire "a1b1", WireInput.wire "m1"]

#eval do
  let (_, _, res1, stats1) := checkDProbing domAND 1
  let (g, _, res2, stats2) := checkDProbing domAND 2
  IO.println "=== Example 3 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println stats1.pp
  IO.println (ppResult res2 2)
  IO.println stats2.pp

/-! ## Example 4

    Two wires whose factored expressions canonicalise to the same NodeId.
    The equivalence rule fires immediately on the second wire when the first
    is in known. -/
def circuit4 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]

#eval do
  let (g, _, res, stats) := checkDProbing circuit4 1
  IO.println "=== Example 4 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 1)
  IO.println stats.pp

/-! ## Example 5 — containment via shared intermediate + equivalence

    w1a = a + r,  w1 = w1a + b   (b is a Public leaf, hence computable)
    w2  = a + r

    Decomposing w1 to 2-ary exposes the intermediate `w1a = a + r`, whose DAG
    node is hash-cons-identical to `w2`.  At order 1, probing w1 alone certifies
    both w1 and w2 in one rewrite call: the XOR backward rule (`tryRule`) sees w1
    known with b computable and exactly one non-computable wire-input (w1a), so
    w1a enters `known`; the equivalence rule then adds w2, since w2 shares w1a's
    NodeId.  This is the faithful 2-ary version of what an n-ary symm-diff rule
    would have done on the inputs directly. -/
def circuit5 : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1a" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "w1"  #[WireInput.wire "w1a", WireInput.leaf (VarType.Public "b")]
  |>.addWireXor "w2"  #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]

#eval do
  let (g, _, res, stats) := checkDProbing circuit5 1
  IO.println "=== Example 5 ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 1)
  IO.println stats.pp

/-! ## Example 6 — Q⁴₁₂ quadratic bijection -/
def circuitF : GlobalDAG := ({} : GlobalDAG)
  -- input shares (atomically encoded; not probe targets)
  |>.addShare "a1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r0")]
  |>.addShare "a2" #[WireInput.leaf (VarType.Random "r0")]
  |>.addShare "b1" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r1")]
  |>.addShare "b2" #[WireInput.leaf (VarType.Random "r1")]
  |>.addShare "c1" #[WireInput.leaf (VarType.Secret "c"), WireInput.leaf (VarType.Random "r2")]
  |>.addShare "c2" #[WireInput.leaf (VarType.Random "r2")]
  |>.addShare "d1" #[WireInput.leaf (VarType.Secret "d"), WireInput.leaf (VarType.Random "r3")]
  |>.addShare "d2" #[WireInput.leaf (VarType.Random "r3")]
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
  |>.addWireXor "z1a" #[WireInput.wire "a1b1", WireInput.wire "a1c1"]
  |>.addWireXor "z1"  #[WireInput.wire "z1a", WireInput.wire "c1"]
  |>.addWireXor "z2" #[WireInput.wire "a1b2", WireInput.wire "a1c2"]
  |>.addWireXor "z3" #[WireInput.wire "a2b1", WireInput.wire "a2c1"]
  |>.addWireXor "z4a" #[WireInput.wire "a2b2", WireInput.wire "a2c2"]
  |>.addWireXor "z4"  #[WireInput.wire "z4a", WireInput.wire "c2"]
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
  let (g, _, res1, stats1) := checkDProbing circuitF 1
  IO.println "=== F: shared Q⁴₁₂ (no extra r) ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println stats1.pp
  let (_, _, res2, stats2) := checkDProbing circuitF 2
  IO.println (ppResult res2 2)
  IO.println stats2.pp


/-! ### Example 7 — DOM-AND with 3 shares -/
def circuitG : GlobalDAG := ({} : GlobalDAG)
  -- input shares (atomically encoded; not probe targets).
  -- 3-sharing: a = a0+a1+a2, b = b0+b1+b2.
  |>.addShare "a0" #[.leaf (.Random "ra0")]
  |>.addShare "a1" #[.leaf (.Random "ra1")]
  |>.addShare "a2" #[.leaf (.Secret "a"), .leaf (.Random "ra0"), .leaf (.Random "ra1")]
  |>.addShare "b0" #[.leaf (.Random "rb0")]
  |>.addShare "b1" #[.leaf (.Random "rb1")]
  |>.addShare "b2" #[.leaf (.Secret "b"), .leaf (.Random "rb0"), .leaf (.Random "rb1")]
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
  -- outputs (each is a diagonal term + two already-masked cross terms)
  |>.addWireXor "s0m" #[.wire "u0", .wire "c01"]
  |>.addWireXor "s0"  #[.wire "s0m", .wire "c02"]
  |>.addWireXor "s1m" #[.wire "u1", .wire "c10"]
  |>.addWireXor "s1"  #[.wire "s1m", .wire "c12"]
  |>.addWireXor "s2m" #[.wire "u2", .wire "c20"]
  |>.addWireXor "s2"  #[.wire "s2m", .wire "c21"]

#eval do
  let (g, _, res1, stats1) := checkDProbing circuitG 1
  let (_, _, res2, stats2) := checkDProbing circuitG 2
  let (_, _, res3, stats3) := checkDProbing circuitG 3
  IO.println "=== G: 3-share DOM-AND ==="
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res1 1)
  IO.println stats1.pp
  IO.println (ppResult res2 2)
  IO.println stats2.pp
  IO.println (ppResult res3 3)
  IO.println stats3.pp

/-! ### Example 8 — DOM-AND with 7 shares -/
partial def addWireXorChain (g : GlobalDAG) (out : String) (terms : Array WireInput) : GlobalDAG :=
  if terms.size == 0 then
    g.addWireXor out #[.const false]
  else if terms.size == 1 then
    g.addWireXor out #[terms[0]!]
  else
    let firstName := if terms.size == 2 then out else s!"{out}m0"
    let g := g.addWireXor firstName #[terms[0]!, terms[1]!]
    let rec go (g : GlobalDAG) (acc : String) (idx : Nat) : GlobalDAG :=
      if idx >= terms.size then g
      else
        let name := if idx + 1 == terms.size then out else s!"{out}m{idx - 1}"
        let g := g.addWireXor name #[.wire acc, terms[idx]!]
        go g name (idx + 1)
    go g firstName 2
def dom7Indices : Array Nat := #[0, 1, 2, 3, 4, 5, 6]
def dom7RandomIndices : Array Nat := #[0, 1, 2, 3, 4, 5]
def dom7Pairs : Array (Nat × Nat) :=
  #[(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 4), (3, 5), (3, 6),
    (4, 5), (4, 6),
    (5, 6)]
def dom7Share (pre : String) (i : Nat) : WireInput :=
  .wire s!"{pre}{i}"
def dom7LastShareInputs (secretName randomPrefix : String) : Array WireInput :=
  dom7RandomIndices.foldl (fun acc i =>
    acc.push (.leaf (.Random s!"{randomPrefix}{i}")))
    #[.leaf (.Secret secretName)]
-- Input shares are registered with `addShare`, matching `circuitG`: they are
-- available algebraically through `.wire "a0"`/`.wire "b0"` references, but are
-- not included in `wireOrder` and therefore are not probe targets.
def addDom7InputSharesFor
    (g : GlobalDAG) (sharePrefix secretName randomPrefix : String) : GlobalDAG :=
  dom7Indices.foldl (fun g i =>
    if i == 6 then
      g.addShare s!"{sharePrefix}{i}" (dom7LastShareInputs secretName randomPrefix)
    else
      g.addShare s!"{sharePrefix}{i}" #[.leaf (.Random s!"{randomPrefix}{i}")])
    g
def addDom7InputShares (g : GlobalDAG) : GlobalDAG :=
  let g := addDom7InputSharesFor g "a" "a" "ra"
  addDom7InputSharesFor g "b" "b" "rb"
def addDom7Diagonals (g : GlobalDAG) : GlobalDAG :=
  dom7Indices.foldl (fun g i =>
    g.addWireAnd s!"u{i}" #[dom7Share "a" i, dom7Share "b" i])
    g
def addDom7CrossProducts (g : GlobalDAG) : GlobalDAG :=
  dom7Pairs.foldl (fun g p =>
    let i := p.1
    let j := p.2
    let g := g.addWireAnd s!"p{i}{j}" #[dom7Share "a" i, dom7Share "b" j]
    g.addWireAnd s!"p{j}{i}" #[dom7Share "a" j, dom7Share "b" i])
    g
def addDom7MaskedCrossTerms (g : GlobalDAG) : GlobalDAG :=
  dom7Pairs.foldl (fun g p =>
    let i := p.1
    let j := p.2
    let r := WireInput.leaf (.Random s!"r{i}{j}")
    let g := g.addWireXor s!"c{i}{j}" #[.wire s!"p{i}{j}", r]
    g.addWireXor s!"c{j}{i}" #[.wire s!"p{j}{i}", r])
    g
def dom7OutputTerms (i : Nat) : Array WireInput :=
  dom7Indices.foldl (fun acc j =>
    if j == i then acc else acc.push (.wire s!"c{i}{j}"))
    #[.wire s!"u{i}"]
def addDom7Outputs (g : GlobalDAG) : GlobalDAG :=
  dom7Indices.foldl (fun g i =>
    addWireXorChain g s!"s{i}" (dom7OutputTerms i))
    g

def circuitH : GlobalDAG :=
  let g : GlobalDAG := {}
  let g := addDom7InputShares g
  let g := addDom7Diagonals g
  let g := addDom7CrossProducts g
  let g := addDom7MaskedCrossTerms g
  addDom7Outputs g

/-
#eval do
  IO.println "=== H: 7-share DOM-AND ==="
  let t0 := (← IO.monoMsNow)
  let (g, _, res, stats) := checkDProbing circuitH 4
  let t1 := (← IO.monoMsNow)
  IO.println s!"[{t1 - t0} ms]"
  IO.println (Circuit.ppCircuit g.circuit)
  IO.println (ppResult res 3)
  IO.println stats.pp

  output:
  === H: 7-share DOM-AND ===
  [1792660 ms]
  SECURE at order 3: all probe sets certified.
    total discharges       : 3223
    successful main probes : 1599
    free wires (sum)       : 921
    free wires (avg/main)  : 0.575985
-/

end verif

-- investigate why closures suck, they shouldn't
-- check whether example 9 would be verified in maskverif
-- check what Barthe does in order not to do redundant work       --> it doesn't do anything
-- reimplement witness replay in place of closures then compare
-- get maskverif working
-- implement the (A, V, k) worklist representation and compare
-- investigate redundant worklist items (due to closures)
