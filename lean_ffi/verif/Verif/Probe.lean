import Verif.«n-aryDAG»
import Verif.Rewrite
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Probe Enumeration

### Worklist structure

    wl = #[ ⟨d_1, e_1⟩, … ]

means "pick d_j wires from group e_j; union = one concrete probe."
Total probes = ∏_j C(|e_j|, d_j).

**Splitting** after extension with safe set S ⊆ e for one factor ⟨d, e⟩:
  - Pure-safe   ⟨d, S⟩        : certified, no recursion.
  - Pure-unsafe ⟨d, e\S⟩      : recurse (single factor).
  - Mixed i/d-i                : for i in 1..d-1,
      recurse as #[⟨i, S⟩, ⟨d-i, e\S⟩].
-/

-- ============================================================
-- §1  Static pre-factoring
-- ============================================================

/-- Pre-factor every registered wire once, storing the stable factored root
    NodeIds in the returned map.  Must be called after all wires are added and
    before any probe begins. -/
def prebuildFactoredWires (gdag : GlobalDAG)
    : GlobalDAG × HashMap String NodeId :=
  gdag.wires.fold (fun (g, fw) name origId =>
    let (dag', facId) := g.dag.factorNode origId
    ({ g with dag := dag' }, fw.insert name facId))
    (gdag, {})

-- ============================================================
-- §2  Witness
-- ============================================================

/-- The rewrite witness for one certified probe: the ordered sequence of
    random-leaf NodeIds rewritten by the rewrite loop.  Portable across all
    probes because random-leaf NodeIds are fixed at circuit-construction time. -/
abbrev Witness := Array NodeId

def extractWitness (ps : ProbeState) : Witness :=
  ps.rewriteHistory.map (·.1)

-- ============================================================
-- §3  Replay
-- ============================================================

/-- Replay witness W on a fresh probe state.
    For each r in W (in order): check that r is standalone in the current probe
    context, then apply the rewrite.  Stop and return false on any failure.

    Correctness across probes: r is a random leaf; its NodeId is stable.
    The XOR parent is found via `ps.parents[r]` — always correct for this probe's
    factored subgraph, regardless of which probe produced W. -/
def replayWitness (gdag : GlobalDAG) (ps : ProbeState) (w : Witness)
    : GlobalDAG × ProbeState × Bool :=
  w.foldl (fun (gdag, ps, ok) r =>
    if !ok then (gdag, ps, false)
    else if !ps.isStandalone r then (gdag, ps, false)
    else
      let (gdag', ps') := applyRewrite gdag ps r
      (gdag', ps', true))
    (gdag, ps, true)

-- ============================================================
-- §4  Worklist
-- ============================================================

/-- One factor of the worklist product.
    Semantics: choose exactly `count` wires from `wires`. -/
structure ProbeFactor where
  count : Nat
  wires : Array String
  deriving Repr

abbrev ProbeWorklist := Array ProbeFactor

def chooseRepresentative (wl : ProbeWorklist) : Array String :=
  wl.foldl (fun acc f => acc ++ f.wires.extract 0 f.count) #[]

def wireNamesToIds (fw : HashMap String NodeId) (names : Array String) : Array NodeId :=
  names.filterMap (fw[·]?)

-- ============================================================
-- §5  Check result
-- ============================================================

inductive CheckResult
  | Secure
  | Insecure : Array String → CheckResult
  deriving Repr, Inhabited

def CheckResult.isSecure : CheckResult → Bool
  | .Secure     => true
  | .Insecure _ => false

-- ============================================================
-- §6  Core probe check
-- ============================================================

/-- Run the full rewrite pipeline on a set of pre-factored root NodeIds. -/
def checkProbeByIds (gdag : GlobalDAG) (ids : Array NodeId)
    : GlobalDAG × ProbeState × Bool :=
  let (gdag', ps) := initProbeByIds gdag ids
  rewriteLoop gdag' ps

-- ============================================================
-- §7  Extend
-- ============================================================

/-- Greedy extension: classify each candidate wire as safe (replay succeeds
    when it is added to the already-certified set) or unsafe (replay fails).

    The certified set grows: safe wires are added before testing subsequent
    candidates.  This matches the paper's Algorithm 4. -/
def extendCertified
    (gdag       : GlobalDAG)
    (fw         : HashMap String NodeId)
    (w          : Witness)
    (certified  : Array String)
    (candidates : Array String)
    : GlobalDAG × Array String × Array String :=
  candidates.foldl (fun (gdag, safe, notsafe) name =>
    let probeNames := certified ++ safe |>.push name
    let probeIds   := wireNamesToIds fw probeNames
    let (gdag', ps)       := initProbeByIds gdag probeIds
    let (gdag'', ps', ok) := replayWitness gdag' ps w
    if ok && isSecure gdag'' ps' then (gdag'', safe.push name, notsafe)
    else                              (gdag'', safe, notsafe.push name))
    (gdag, #[], #[])

-- ============================================================
-- §8  CheckAll (mutually recursive)
-- ============================================================

mutual
partial def checkAllSingle (gdag  : GlobalDAG) (fw : HashMap String NodeId) (count : Nat) (wires : Array String)
  : GlobalDAG × CheckResult :=
  if count == 0 || wires.isEmpty || count > wires.size then (gdag, .Secure)
  else
    -- OptSampling: union probe.
    let allIds := wireNamesToIds fw wires
    let (gdag, _, allSec) := checkProbeByIds gdag allIds
    if allSec then (gdag, .Secure)
    else
      -- Representative.
      let repNames := wires.extract 0 count
      let repIds   := wireNamesToIds fw repNames
      let (gdag, repPs, repSec) := checkProbeByIds gdag repIds
      if !repSec then (gdag, .Insecure repNames)
      else
        let w         := extractWitness repPs
        let remaining := wires.extract count wires.size
        -- Extend.
        let (gdag, safe, notsafe) := extendCertified gdag fw w repNames remaining
        -- Pure-unsafe recursion.
        let (gdag, r1) := checkAllSingle gdag fw count notsafe
        if !r1.isSecure then (gdag, r1)
        else
          -- Mixed splits.
          let allSafe := repNames ++ safe
          let rec doMixed (gdag : GlobalDAG) (i : Nat) : GlobalDAG × CheckResult :=
            if i == 0 then (gdag, .Secure)
            else
              let (gdag, ri) := checkAllMulti gdag fw
                #[{ count := i,          wires := allSafe },
                  { count := count - i,  wires := notsafe  }]
              if !ri.isSecure then (gdag, ri) else doMixed gdag (i - 1)
          doMixed gdag (count - 1)

partial def checkAllMulti (gdag : GlobalDAG) (fw : HashMap String NodeId) (wl : ProbeWorklist)
  : GlobalDAG × CheckResult :=
  let wl := wl.filter (fun f => f.count > 0 && f.wires.size >= f.count)
  if wl.isEmpty then (gdag, .Secure)
  else
    -- OptSampling on the full union.
    let allWires := wl.foldl (fun acc f => acc ++ f.wires) #[]
    let allIds   := wireNamesToIds fw allWires
    let (gdag, _, allSec) := checkProbeByIds gdag allIds
    if allSec then (gdag, .Secure)
    else
      -- Representative: first `count` from each factor.
      let repNames := chooseRepresentative wl
      let repIds   := wireNamesToIds fw repNames
      let (gdag, repPs, repSec) := checkProbeByIds gdag repIds
      if !repSec then (gdag, .Insecure repNames)
      else
        let w := extractWitness repPs
        -- Extend each factor.  Certified base = all other factors' representatives.
        let (gdag, newWl) :=
          wl.foldl (fun (gdag, acc) f =>
            let fRep      := f.wires.extract 0 f.count
            let fRest     := f.wires.extract f.count f.wires.size
            let otherReps := repNames.filter (fun n => !fRep.contains n)
            let (gdag, _, fUnsafe) :=
              extendCertified gdag fw w (otherReps ++ fRep) fRest
            (gdag, acc.push { count := f.count, wires := fUnsafe }))
            (gdag, #[])
        -- Recurse on the unsafe Cartesian product.
        checkAllMulti gdag fw newWl
end
/-!
Single-factor CheckAll.  Handles one factor ⟨count, wires⟩.

```
checkAllSingle(count, wires):
  if vacuous: return Secure

  -- OptSampling
  if checkProbe(all wires) is Secure: return Secure

  -- Representative probe
  rep ← wires[0..count]
  if checkProbe(rep) is Insecure: return Insecure(rep)
  W ← extractWitness

  -- Extend
  (safe, unsafe) ← extendCertified(W, rep, wires[count..])

  -- Recurse: pure-unsafe
  r1 ← checkAllSingle(count, unsafe)
  if Insecure: return r1

  -- Recurse: mixed splits
  allSafe ← rep ++ safe
  for i in 1..count-1:
    ri ← checkAllMulti(#[⟨i, allSafe⟩, ⟨count-i, unsafe⟩])
    if Insecure: return ri

  return Secure
```
-/

-- ============================================================
-- §9  Public entry point
-- ============================================================

/-- Check d-probing security of the circuit.
    Pre-factors all wires, then runs CheckAll on ⟨probingOrder, allWires⟩.

    `.Secure`         every probe of size ≤ probingOrder is certified.
    `.Insecure names` a probe set that could not be certified (true attack or
                      engine limitation — polynomial solver needed as next step). -/
def checkDProbingSecurity (gdag : GlobalDAG) (probingOrder : Nat)
    : GlobalDAG × HashMap String NodeId × CheckResult :=
  let (gdag, fw) := prebuildFactoredWires gdag
  -- Collect wire names in a deterministic order.
  let allWires := gdag.wires.fold (fun acc name _ => acc.push name) #[]
  let (gdag, result) := checkAllSingle gdag fw probingOrder allWires
  (gdag, fw, result)

-- ============================================================
-- §10  Pretty printing
-- ============================================================

def ppResult (gdag : GlobalDAG) (fw : HashMap String NodeId)
    (result : CheckResult) (order : Nat) : String :=
  match result with
  | .Secure =>
    s!"SECURE at order {order}: all probe sets certified."
  | .Insecure names =>
    let label := "{" ++ String.intercalate ", " names.toList ++ "}"
    let ids   := wireNamesToIds fw names
    let exprs := ids.toList.map gdag.dag.ppNode |> String.intercalate ",  "
    s!"INSECURE at order {order}: counterexample {label}\n  Exprs: [{exprs}]"

-- ============================================================
-- §11  Examples
-- ============================================================

/-! ### Example A — unmasked secret, insecure at order 1 -/
def circuitA : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a) := g.mkLeaf (.Secret "a")
  let (g, w) := g.mkXor #[a]
  g.addWire "w" w

def exampleA : IO Unit := do
  IO.println "=== A: unmasked secret ==="
  let (gdag, fw, r) := checkDProbingSecurity circuitA 1
  IO.println (ppResult gdag fw r 1); IO.println ""

#eval exampleA
-- INSECURE at order 1: counterexample {w}

/-! ### Example B — first-order masking, secure at order 1 -/
def circuitB : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a) := g.mkLeaf (.Secret "a")
  let (g, r) := g.mkLeaf (.Random "r")
  let (g, w) := g.mkXor #[a, r]
  g.addWire "w" w

def exampleB : IO Unit := do
  IO.println "=== B: first-order masked ==="
  let (gdag, fw, r) := checkDProbingSecurity circuitB 1
  IO.println (ppResult gdag fw r 1); IO.println ""

#eval exampleB
-- SECURE at order 1

/-! ### Example C — DOM-AND: secure at order 1, insecure (rewrite-only) at order 2

    s0 = a0·b0 ⊕ a0·b1 ⊕ r
    s1 = a1·b0 ⊕ a1·b1 ⊕ r

    Order 1: r is standalone in each single-wire probe (after factoring by a0 or a1).
    Order 2: {s0, s1} — r has two XOR parents, rewrite engine cannot certify.
             (A polynomial solver would handle this; beyond our scope here.) -/
def domAND2 : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, a0) := g.mkLeaf (.Secret "a0")
  let (g, a1) := g.mkLeaf (.Secret "a1")
  let (g, b0) := g.mkLeaf (.Secret "b0")
  let (g, b1) := g.mkLeaf (.Secret "b1")
  let (g, r)  := g.mkLeaf (.Random "r")
  let (g, a0b0) := g.mkAnd #[a0, b0]
  let (g, a0b1) := g.mkAnd #[a0, b1]
  let (g, a1b0) := g.mkAnd #[a1, b0]
  let (g, a1b1) := g.mkAnd #[a1, b1]
  let (g, s0)   := g.mkXor #[a0b0, a0b1, r]
  let (g, s1)   := g.mkXor #[a1b0, a1b1, r]
  (g.addWire "s0" s0).addWire "s1" s1

def exampleC : IO Unit := do
  IO.println "=== C: DOM-AND ==="
  let (gdag1, fw1, r1) := checkDProbingSecurity domAND2 1
  IO.println (ppResult gdag1 fw1 r1 1)
  let (gdag2, fw2, r2) := checkDProbingSecurity domAND2 2
  IO.println (ppResult gdag2 fw2 r2 2)
  IO.println ""

#eval exampleC
-- Order 1: SECURE
-- Order 2: INSECURE (counterexample: the first pair tried, e.g. {s0, s1})

/-! ### Example D — cross-probe sharing: three wires, two randoms

    w1 = e·a ⊕ r0,  w2 = e·b ⊕ r0,  w3 = e·c ⊕ r1

    Order 1: each wire alone is secure.
    Order 2: {w1, w2} shares r0 — insecure.
             {w1, w3} and {w2, w3} use distinct randoms — secure.

    CheckAll at order 2:
    - OptSampling on {w1,w2,w3}: r0 has 2 XOR parents, r1 has 1 — partial rewrite
      possible but not all secrets cleared → union probe not secure.
    - Representative = {w1, w2} (first two): insecure → counterexample returned.

    This demonstrates the early-exit behaviour: the algorithm finds the
    counterexample immediately without examining all C(3,2)=3 pairs. -/
def circuitD : GlobalDAG :=
  let g : GlobalDAG := {}
  let (g, e)  := g.mkLeaf (.Public "e")
  let (g, a)  := g.mkLeaf (.Secret "a")
  let (g, b)  := g.mkLeaf (.Secret "b")
  let (g, c)  := g.mkLeaf (.Secret "c")
  let (g, r0) := g.mkLeaf (.Random "r0")
  let (g, r1) := g.mkLeaf (.Random "r1")
  let (g, ea) := g.mkAnd #[e, a]
  let (g, eb) := g.mkAnd #[e, b]
  let (g, ec) := g.mkAnd #[e, c]
  let (g, w1) := g.mkXor #[ea, r0]
  let (g, w2) := g.mkXor #[eb, r0]
  let (g, w3) := g.mkXor #[ec, r1]
  ((g.addWire "w1" w1).addWire "w2" w2).addWire "w3" w3

def exampleD : IO Unit := do
  IO.println "=== D: three wires, shared r0 ==="
  let (gdag1, fw1, r1) := checkDProbingSecurity circuitD 1
  IO.println (ppResult gdag1 fw1 r1 1)
  let (gdag2, fw2, r2) := checkDProbingSecurity circuitD 2
  IO.println (ppResult gdag2 fw2 r2 2)
  IO.println ""

#eval exampleD

end verif
