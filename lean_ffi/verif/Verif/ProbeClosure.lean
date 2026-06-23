import Verif.«n-aryDAG»
import Verif.Rewrite
import Verif.WitnessReplay
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Probe Enumeration with maskVerif Witness Replay

The subset-space exploration (`checkAllSingle`/`checkAllMulti`) is maskVerif's
worklist space-splitting (Barthe et al. 2015, Algorithm 6 / 2019 `check_all`).
The safe-set *extension* it relies on is provided by witness replay
(`WitnessReplay.lean`): a certified representative tuple leaves a replayable
optimistic-sampling witness, which is replayed on the remaining candidates to
grow the safe set `ŷ`.  This replaces the earlier topological-greedy closure;
`Stats` keeps its field names and output format (where "closure" now denotes the
replay-extended safe set `ŷ`) so results stay directly comparable across the
closure and witness-replay branches.
-/

-- ============================================================
-- Stats
-- ============================================================

/-- Canonical key of a *set* of wire names: dedup + sort + join.  Two probe sets
    (or closures) equal as sets map to the same key regardless of insertion order
    or multiplicity, so they can be looked up for redundancy. -/
def setKey (names : Array String) : String :=
  let sorted := names.qsort (fun a b => a < b)
  let deduped := sorted.foldl (fun acc w =>
    if acc.isEmpty || acc[acc.size - 1]! != w then acc.push w else acc)
    (#[] : Array String)
  String.intercalate "\n" deduped.toList

/-- Which kind of discharge a probe set came from: the OptSampling large-set
    `union` test, or a size-`d` `chosen` main probe.  Lets a repeat be attributed
    to the discharge that actually re-did the work. -/
inductive DischargeKind
  | union
  | chosen
  deriving Repr, Inhabited

/-- One producer of a certified closure: the `chosen` size-`d` probe set that
    yielded it, and a rendering of the `worklist` item(s) that produced that probe
    set.  Used to report closure collisions (cause B) — distinct chosen sets that
    drain to one and the same closure. -/
structure ClosureWitness where
  chosen   : Array String
  worklist : String
  deriving Inhabited

structure Stats where
  totalDischarges     : Nat := 0
  successMain         : Nat := 0
  freeWiresSum        : Nat := 0
  /-- Repeated *union* (OptSampling large-set) discharges: a whole wire-collection
      re-sent to the engine after it was already discharged.  This is the dominant
      cause of redundancy — e.g. `checkAllMulti` re-discharging the reconstituted
      `wires` set after the safe/unsafe split. -/
  redundantUnionDischarges  : Nat := 0
  /-- Repeated *chosen* (size-`d` main probe) discharges: the same chosen probe
      re-sent.  Expected to be rare, since the space-split keeps chosen probes
      distinct (it is bounded above by `redundantClosures`). -/
  redundantChosenDischarges : Nat := 0
  /-- Certified closures whose set of wires was already certified earlier.  This
      is cause (B) — a *different* chosen probe set whose closure (and hence the
      region of the observation space it covers) coincides with an earlier one. -/
  redundantClosures   : Nat := 0
  /-- Verdict memo: maps every distinct probe set (by `setKey`) to its
      secure/insecure verdict, so a repeat is served from here instead of
      re-running the rewrite engine. -/
  verdictCache        : HashMap String Bool := {}
  /-- Maps each certified closure (by `setKey`) to the distinct `chosen` probe
      sets that produced it.  Keys = distinct closures; values with ≥2 entries are
      the closure collisions: different `d`-wire probes draining to one closure. -/
  closureWitnesses    : HashMap String (Array ClosureWitness) := {}

namespace Stats

/-- Record a *memo hit*: a probe set already in `verdictCache`, served without
    re-running the engine.  Bumps `totalDischarges` (it is still a logical
    discharge) and the repeat counter for `kind` (the engine run it avoided). -/
def recordHit (s : Stats) (kind : DischargeKind) : Stats :=
  let s := { s with totalDischarges := s.totalDischarges + 1 }
  match kind with
  | .union  => { s with redundantUnionDischarges  := s.redundantUnionDischarges  + 1 }
  | .chosen => { s with redundantChosenDischarges := s.redundantChosenDischarges + 1 }

/-- Record a *memo miss*: a probe set discharged for the first time.  Bumps
    `totalDischarges` and stores its `verdict` for future lookups. -/
def recordMiss (s : Stats) (key : String) (verdict : Bool) : Stats :=
  { s with totalDischarges := s.totalDischarges + 1
           verdictCache    := s.verdictCache.insert key verdict }

/-- Record one certified `closure`, produced by probe set `chosen` coming from
    `worklist`.  Bumps `redundantClosures` when this closure was certified before,
    and remembers the *distinct* chosen probe sets behind each closure so that the
    collisions (cause B) can be reported. -/
def recordClosure (s : Stats) (closure chosen : Array String) (worklist : String) : Stats :=
  let key := setKey closure
  let w : ClosureWitness := { chosen, worklist }
  match s.closureWitnesses[key]? with
  | none    =>
    { s with closureWitnesses := s.closureWitnesses.insert key #[w] }
  | some ws =>
    let chosenKey := setKey chosen
    let ws' := if ws.any (fun u => setKey u.chosen == chosenKey) then ws else ws.push w
    { s with redundantClosures := s.redundantClosures + 1
             closureWitnesses  := s.closureWitnesses.insert key ws' }

@[inline] def addSuccess (s : Stats) (free : Nat) : Stats :=
  { s with successMain  := s.successMain + 1
           freeWiresSum := s.freeWiresSum + free }

def avgFreeWires (s : Stats) : Float :=
  if s.successMain == 0 then 0.0
  else Float.ofNat s.freeWiresSum / Float.ofNat s.successMain

/-- Render the closure collisions: closures certified by ≥2 distinct chosen probe
    sets, with the producing probe set and worklist item for each.  Empty string
    when there are none. -/
def ppClosureCollisions (s : Stats) : String :=
  let setStr (xs : List String) : String := "{" ++ String.intercalate ", " xs ++ "}"
  let collisions := s.closureWitnesses.toList.filter (fun (_, ws) => ws.size >= 2)
  if collisions.isEmpty then ""
  else
    let body := collisions.map (fun (key, ws) =>
      let producers := ws.toList.map (fun w =>
        "      chosen " ++ setStr w.chosen.toList ++ "  from worklist [" ++ w.worklist ++ "]")
      "    closure " ++ setStr (key.splitOn "\n") ++ " (" ++ toString ws.size
        ++ " distinct probes):\n" ++ String.intercalate "\n" producers)
    "\n  closure collisions (" ++ toString collisions.length ++ "):\n"
      ++ String.intercalate "\n" body

def pp (s : Stats) : String :=
  s!"  total discharges       : {s.totalDischarges}\n  distinct probe sets    : {s.verdictCache.size}\n  repeated discharges    : {s.redundantUnionDischarges + s.redundantChosenDischarges}  (union {s.redundantUnionDischarges}, chosen {s.redundantChosenDischarges})\n  distinct closures      : {s.closureWitnesses.size}\n  repeated closures      : {s.redundantClosures}\n  successful main probes : {s.successMain}\n  free wires (sum)       : {s.freeWiresSum}\n  free wires (avg/main)  : {s.avgFreeWires}" ++ s.ppClosureCollisions

end Stats

-- ============================================================
-- Worklist, check result, discharge
-- ============================================================

structure ProbeFactor where
  count : Nat
  wires : Array String
  deriving Repr, Inhabited

abbrev ProbeWorklist := Array ProbeFactor

/-- Compact rendering of a worklist for the collision report: each factor as
    `count of {wires}`, factors separated by `;`. -/
def ppFactor (f : ProbeFactor) : String :=
  toString f.count ++ " of {" ++ String.intercalate ", " f.wires.toList ++ "}"
def ppWorklist (wl : ProbeWorklist) : String :=
  String.intercalate " ; " (wl.toList.map ppFactor)

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
    (stats : Stats) (kind : DischargeKind) (names : Array String)
    : GlobalDAG × ProbeState × Bool × Stats :=
  let key := setKey names
  match stats.verdictCache[key]? with
  | some sec => (g, (default : ProbeState), sec, stats.recordHit kind)
  | none     =>
    let ids := wireNamesToIds fw names
    let (g, ps) := initProbeByIds g ids
    let (g, ps, sec) := rewriteLoop g ps
    if sec then (g, ps, true, stats.recordMiss key true)
    else
      let (g, sec2) := checkProbeComplete g ps.roots
      (g, ps, sec2, stats.recordMiss key sec2)

-- ============================================================
-- Representative tuple
-- ============================================================

/-- The representative probe tuple of a worklist (maskVerif's `lfirst`): the
    first `count` wires of each factor, in order.  This is the tuple sent to the
    witness-capturing checker; the witness it yields is then replayed on the
    remaining candidates to grow the safe set. -/
def buildProbeSimple (wl : ProbeWorklist) : Array String :=
  wl.foldl (fun acc f => acc ++ f.wires.extract 0 f.count) #[]

/-- Resolve the candidate wires (those present in the DAG) to `(name, NodeId)`
    pairs for witness replay. -/
@[inline]
def candidatesOf (fw : HashMap String NodeId) (wires : Array String)
    : Array (String × NodeId) :=
  wires.filterMap (fun w => (fw[w]?).map (fun nid => (w, nid)))

/-- Certify the representative `chosen` tuple and return its replay witness,
    threading `Stats` like a `.chosen` discharge.  On a verdict-cache hit the
    witness is still recomputed (the cache stores only the boolean), which is
    rare since the space-split keeps chosen probes distinct. -/
def checkChosenWithWitness (g : GlobalDAG) (fw : HashMap String NodeId)
    (stats : Stats) (chosen : Array String)
    : GlobalDAG × Bool × Witness × Stats :=
  let ids := wireNamesToIds fw chosen
  let key := setKey chosen
  let (g, sec, witness) := checkWithWitness g ids
  let stats := match stats.verdictCache[key]? with
    | some _ => stats.recordHit .chosen
    | none   => stats.recordMiss key sec
  (g, sec, witness, stats)

-- ============================================================
-- CheckAll: same recursion structure, threaded with Stats
-- ============================================================

mutual

partial def checkAllSingle
    (g : GlobalDAG) (fw : HashMap String NodeId)
    (stats : Stats) (count : Nat) (wires : Array String) (extend : Bool)
    : GlobalDAG × Stats × CheckResult :=
  if count == 0 then (g, stats, .Secure)
  else if wires.size < count then (g, stats, .Secure)
  else
    -- OptSampling union discharge.
    let (g, _, allSec, stats) := checkProbeByNames g fw stats .union wires
    if allSec then (g, stats, .Secure)
    else
      let wl0 : ProbeWorklist := #[{ count, wires }]
      -- Certify the representative tuple and capture its replay witness.
      let chosen := buildProbeSimple wl0
      let (g, chosenSec, witness, stats) := checkChosenWithWitness g fw stats chosen
      if !chosenSec then (g, stats, .Insecure chosen)
      else
        -- Grow the safe set ŷ: by witness replay (`extend`), or, in the naive
        -- baseline, leave it as the chosen tuple itself (no extension).
        let (g, safe) :=
          if extend then extendByReplay g witness (candidatesOf fw wires)
          else (g, chosen)
        let free  := safe.size - chosen.size
        let stats := stats.addSuccess free
        let stats := stats.recordClosure safe chosen (ppWorklist wl0)
        let safeSet : HashMap String Unit :=
          safe.foldl (fun m w => m.insert w ()) {}
        let unsafeWires := wires.filter (fun w => !safeSet.contains w)
        let (g, stats, r1) := checkAllSingle g fw stats count unsafeWires extend
        if !r1.isSecure then (g, stats, r1)
        else
          let safeWithinWires := wires.filter (fun w => safeSet.contains w)
          let rec doMixed (g : GlobalDAG) (stats : Stats) (i : Nat)
              : GlobalDAG × Stats × CheckResult :=
            if i == 0 then (g, stats, .Secure)
            else
              let (g, stats, ri) := checkAllMulti g fw stats
                #[{ count := i,         wires := safeWithinWires },
                  { count := count - i, wires := unsafeWires }] extend
              if !ri.isSecure then (g, stats, ri)
              else doMixed g stats (i - 1)
          doMixed g stats (count - 1)

partial def checkAllMulti
    (g : GlobalDAG) (fw : HashMap String NodeId)
    (stats : Stats) (wl : ProbeWorklist) (extend : Bool)
    : GlobalDAG × Stats × CheckResult :=
  if isWorklistVacuous wl then (g, stats, .Secure)
  else
    let wl := cleanWorklist wl
    if wl.isEmpty then (g, stats, .Secure)
    else if wl.size == 1 then
      checkAllSingle g fw stats wl[0]!.count wl[0]!.wires extend
    else
      let allWires := wl.foldl (fun acc f => acc ++ f.wires) #[]
      let (g, _, allSec, stats) := checkProbeByNames g fw stats .union allWires
      if allSec then (g, stats, .Secure)
      else
        let chosen := buildProbeSimple wl
        let (g, chosenSec, witness, stats) := checkChosenWithWitness g fw stats chosen
        if !chosenSec then (g, stats, .Insecure chosen)
        else
          let (g, safe) :=
            if extend then extendByReplay g witness (candidatesOf fw allWires)
            else (g, chosen)
          let free  := safe.size - chosen.size
          let stats := stats.addSuccess free
          let stats := stats.recordClosure safe chosen (ppWorklist wl)
          let safeSet : HashMap String Unit :=
            safe.foldl (fun m w => m.insert w ()) {}
          let unsafeWl : ProbeWorklist := wl.map (fun f =>
            { count := f.count
              wires := f.wires.filter (fun w => !safeSet.contains w) })
          let (g, stats, r1) := checkAllMulti g fw stats unsafeWl extend
          if !r1.isSecure then (g, stats, r1)
          else
            let rec splitFactor (g : GlobalDAG) (stats : Stats) (jIdx : Nat)
                : GlobalDAG × Stats × CheckResult :=
              if jIdx >= wl.size then (g, stats, .Secure)
              else
                let f := wl[jIdx]!
                let safeJ   := f.wires.filter (fun w => safeSet.contains w)
                let unsafeJ := f.wires.filter (fun w => !safeSet.contains w)
                let rec doI (g : GlobalDAG) (stats : Stats) (i : Nat)
                    : GlobalDAG × Stats × CheckResult :=
                  if i == 0 then splitFactor g stats (jIdx + 1)
                  else
                    let newWl : ProbeWorklist :=
                      (wl.extract 0 jIdx)
                        ++ #[{ count := i,           wires := safeJ },
                             { count := f.count - i, wires := unsafeJ }]
                        ++ (wl.extract (jIdx + 1) wl.size)
                    let (g, stats, ri) := checkAllMulti g fw stats newWl extend
                    if !ri.isSecure then (g, stats, ri)
                    else doI g stats (i - 1)
                doI g stats (f.count - 1)
            splitFactor g stats 0

end

-- ============================================================
-- Public entry point
-- ============================================================

/-- Verify `probingOrder`-probing security.  `extend := true` uses maskVerif
    witness replay to grow each certified probe set; `extend := false` is the
    naive baseline that performs no extension (each representative covers only
    its own subsets), degrading the space-split toward exhaustive enumeration. -/
def checkDProbing (g : GlobalDAG) (probingOrder : Nat) (extend : Bool := true)
    : GlobalDAG × HashMap String NodeId × CheckResult × Stats :=
  let fw := g.wires
  let allWires := g.circuit.wireOrder
  let (g, stats, res) := checkAllSingle g fw {} probingOrder allWires extend
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

-- helper function to build a chain of XORs from an array of terms for some examples
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


/-! ## Example 1 — first-order masked wire, secure at order 1 -/
def circuitA : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]


/-! ## Example 2 — XOR linear dependency between wires

    w1 = a + r1,  w2 = b + r2,  w3 = w1 + w2

    Probing w3 alone is secure (uniform via r1, r2). At order 2, probing
    {w1, w3} unlocks w2 via the XOR backward rule at w3's def — `tryRule`
    (driven by `drainWorklist`) sees w3 known, all leaf inputs computable
    (there are none), exactly one non-computable wire-input (w2), so w2
    enters known. -/
def circuitB : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r1")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "b"), WireInput.leaf (VarType.Random "r2")]
  |>.addWireXor "w3" #[WireInput.wire "w1", WireInput.wire "w2"]


/-! ## Example 3 — DOM-AND -/
def twoDomAND : GlobalDAG := ({} : GlobalDAG)
  -- Input shares of a and b.
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


/-! ## Example 4

    Two wires whose factored expressions canonicalise to the same NodeId.
    The equivalence rule fires immediately on the second wire when the first
    is in known. -/
def circuitC : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]


/-! ## Example 5 — containment via shared random (witness replay)

    w1a = a + r,  w1 = w1a + b   (b is a Public leaf)
    w2  = a + r

    Decomposing w1 to 2-ary exposes the intermediate `w1a = a + r`, whose DAG
    node is hash-cons-identical to `w2`.  At order 1, probing w1 alone certifies
    both w1 and w2 in one rewrite call: the XOR backward rule (`tryRule`) sees w1
    known with b computable and exactly one non-computable wire-input (w1a), so
    w1a enters `known`; the equivalence rule then adds w2, since w2 shares w1a's
    NodeId.  This is the faithful 2-ary version of what an n-ary symm-diff rule
    would have done on the inputs directly. -/
def circuitD : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1a" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "w1"  #[WireInput.wire "w1a", WireInput.leaf (VarType.Public "b")]
  |>.addWireXor "w2"  #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]


/-! ## Example 6 — Q⁴₁₂ quadratic bijection -/
def q_12 : GlobalDAG := ({} : GlobalDAG)
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


/-! ## Example 7 — DOM-AND with 3 shares -/
def threeDomAND : GlobalDAG := ({} : GlobalDAG)
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

/-! ## Example 8 — DOM-AND with 7 shares -/
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

def sevenDomAND : GlobalDAG :=
  let g : GlobalDAG := {}
  let g := addDom7InputShares g
  let g := addDom7Diagonals g
  let g := addDom7CrossProducts g
  let g := addDom7MaskedCrossTerms g
  addDom7Outputs g

/-! ## Example 9 — 4-share masking of the quadratic function F(x,y,z) = x + (y * z)

    This is a 4-share Threshold Implementation of a quadratic Boolean
    function in three input variables.

    Construction:
      Inputs: three secrets x, y, z, each in 4 shares.

      Output shares:
        F_1 = x_2 + ∑_{i,j ∈ {2,3,4}} y_i * z_j
        F_2 = x_3 + y_1 * z_3 + y_1 * z_4 + y_3 * z_1
                  + y_4 * z_1 + y_1 * z_1
        F_3 = x_4 + y_1 * z_2 + y_2 * z_1
        F_4 = x_1

      Correctness: ∑_i F_i = x + y * z -/
def circuitE : GlobalDAG :=
  let g : GlobalDAG := ({} : GlobalDAG)
  -- share production for x
  |>.addShare "x1" #[WireInput.leaf (VarType.Random "r_x0")]
  |>.addShare "x2" #[WireInput.leaf (VarType.Random "r_x1")]
  |>.addShare "x3" #[WireInput.leaf (VarType.Random "r_x2")]
  |>.addShare "x4" #[WireInput.leaf (VarType.Secret "x"),
                     WireInput.leaf (VarType.Random "r_x0"),
                     WireInput.leaf (VarType.Random "r_x1"),
                     WireInput.leaf (VarType.Random "r_x2")]
  -- share production for y
  |>.addShare "y1" #[WireInput.leaf (VarType.Random "r_y0")]
  |>.addShare "y2" #[WireInput.leaf (VarType.Random "r_y1")]
  |>.addShare "y3" #[WireInput.leaf (VarType.Random "r_y2")]
  |>.addShare "y4" #[WireInput.leaf (VarType.Secret "y"),
                     WireInput.leaf (VarType.Random "r_y0"),
                     WireInput.leaf (VarType.Random "r_y1"),
                     WireInput.leaf (VarType.Random "r_y2")]
  -- share production for z
  |>.addShare "z1" #[WireInput.leaf (VarType.Random "r_z0")]
  |>.addShare "z2" #[WireInput.leaf (VarType.Random "r_z1")]
  |>.addShare "z3" #[WireInput.leaf (VarType.Random "r_z2")]
  |>.addShare "z4" #[WireInput.leaf (VarType.Secret "z"),
                     WireInput.leaf (VarType.Random "r_z0"),
                     WireInput.leaf (VarType.Random "r_z1"),
                     WireInput.leaf (VarType.Random "r_z2")]
  -- all 16 cross-products y_i * z_j
  |>.addWireAnd "y2z2" #[WireInput.wire "y2", WireInput.wire "z2"]
  |>.addWireAnd "y2z3" #[WireInput.wire "y2", WireInput.wire "z3"]
  |>.addWireAnd "y2z4" #[WireInput.wire "y2", WireInput.wire "z4"]
  |>.addWireAnd "y3z2" #[WireInput.wire "y3", WireInput.wire "z2"]
  |>.addWireAnd "y3z3" #[WireInput.wire "y3", WireInput.wire "z3"]
  |>.addWireAnd "y3z4" #[WireInput.wire "y3", WireInput.wire "z4"]
  |>.addWireAnd "y4z2" #[WireInput.wire "y4", WireInput.wire "z2"]
  |>.addWireAnd "y4z3" #[WireInput.wire "y4", WireInput.wire "z3"]
  |>.addWireAnd "y4z4" #[WireInput.wire "y4", WireInput.wire "z4"]
  |>.addWireAnd "y1z3" #[WireInput.wire "y1", WireInput.wire "z3"]
  |>.addWireAnd "y1z4" #[WireInput.wire "y1", WireInput.wire "z4"]
  |>.addWireAnd "y3z1" #[WireInput.wire "y3", WireInput.wire "z1"]
  |>.addWireAnd "y4z1" #[WireInput.wire "y4", WireInput.wire "z1"]
  |>.addWireAnd "y1z1" #[WireInput.wire "y1", WireInput.wire "z1"]
  |>.addWireAnd "y1z2" #[WireInput.wire "y1", WireInput.wire "z2"]
  |>.addWireAnd "y2z1" #[WireInput.wire "y2", WireInput.wire "z1"]
  -- output shares
  let g := addWireXorChain g "F1" #[WireInput.wire "x2",
                       WireInput.wire "y2z2", WireInput.wire "y2z3", WireInput.wire "y2z4",
                       WireInput.wire "y3z2", WireInput.wire "y3z3", WireInput.wire "y3z4",
                       WireInput.wire "y4z2", WireInput.wire "y4z3", WireInput.wire "y4z4"]
  let g := addWireXorChain g "F2" #[WireInput.wire "x3",
                       WireInput.wire "y1z3", WireInput.wire "y1z4",
                       WireInput.wire "y3z1", WireInput.wire "y4z1",
                       WireInput.wire "y1z1"]
  let g := addWireXorChain g "F3" #[WireInput.wire "x4",
                       WireInput.wire "y1z2", WireInput.wire "y2z1"]
  addWireXorChain g "F4" #[WireInput.wire "x1"]

/-! ## Comparison: witness replay vs. the naive (no-extension) baseline

    Runs each instance twice — once with maskVerif witness replay growing every
    certified probe set (`extend := true`), once with no extension at all
    (`extend := false`), where each representative covers only its own subsets and
    the space-split degrades toward exhaustive enumeration.  Both use the same
    sound rewrite checker, so the verdicts can only diverge as `replay secure /
    naive insecure`: a tuple the naive direct check fails to certify on its own,
    but which replay certifies via a representative's witness. -/
def ppAblation (name : String) (g : GlobalDAG) (order : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (_, _, resR, sR) := checkDProbing g order true
  let t1 ← IO.monoMsNow
  let (_, _, resN, sN) := checkDProbing g order false
  let t2 ← IO.monoMsNow
  let v := fun (r : CheckResult) => if r.isSecure then "secure" else "INSECURE"
  IO.println s!"{name} @ order {order}:  witness replay {v resR}  |  naive {v resN}  (agree={resR.isSecure == resN.isSecure})"
  IO.println s!"    witness replay : {t1 - t0} ms\n{sR.pp}\n"
  IO.println s!"    no extension   : {t2 - t1} ms\n{sN.pp}\n"


#eval do
  IO.println "=== Results ==="
  ppAblation "Example 1" circuitA 1
  ppAblation "Example 2" circuitB 1
  ppAblation "Example 2" circuitB 2
  ppAblation "2-share DOM-AND" twoDomAND 1
  ppAblation "2-share DOM-AND" twoDomAND 2
  ppAblation "Example 4" circuitC 1
  ppAblation "Example 4" circuitC 2
  ppAblation "Example 5" circuitD 1
  ppAblation "Q⁴₁₂" q_12 1
  ppAblation "3-share DOM-AND" threeDomAND 2
  -- ppAblation "7-share DOM-AND" sevenDomAND 5
  ppAblation "Example x + yz" circuitE 2
  ppAblation "Example x + yz" circuitE 3

end verif
