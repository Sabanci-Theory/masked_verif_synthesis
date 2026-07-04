import Verif.Coupling
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Wire-Level Probe Enumeration with Coupling-Driven Extension

The probe space is searched with the same OptSampling / space-split structure as
before; the safe-set *provider* is the coupling extension (`couplingExtend`):
after the chosen probe is certified, every candidate wire the certifying coupling
`T` also blinds joins the certified-safe set.  `checkDProbing`'s `extend` flag
toggles this against the naive baseline (`extend := false`, no extension — each
representative covers only its own subsets), for ablation.
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

/-- One producer of a certified extension (safe set): the `chosen` size-`d` probe
    set that yielded it, and a rendering of the `worklist` item(s) that produced
    that probe set.  Used to report extension collisions (cause B) — distinct
    chosen sets whose extension coincides. -/
structure ExtensionWitness where
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
      distinct (it is bounded above by `redundantExtensions`). -/
  redundantChosenDischarges : Nat := 0
  /-- Certified extensions (safe sets) whose set of wires was already certified
      earlier.  This is cause (B) — a *different* chosen probe set whose extension
      (and hence the region of the observation space it covers) coincides with an
      earlier one. -/
  redundantExtensions : Nat := 0
  /-- Verdict memo: maps every distinct probe set (by `setKey`) to its
      secure/insecure verdict, so a repeat is served from here instead of
      re-running the rewrite engine. -/
  verdictCache        : HashMap String Bool := {}
  /-- Maps each certified extension (by `setKey`) to the distinct `chosen` probe
      sets that produced it.  Keys = distinct extensions; values with ≥2 entries
      are the extension collisions: different `d`-wire probes yielding one safe set. -/
  extensionWitnesses  : HashMap String (Array ExtensionWitness) := {}
  anfFallbacks        : Nat := 0
  deriving Inhabited

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

/-- Record one certified `extension` (safe set), produced by probe set `chosen`
    coming from `worklist`.  Bumps `redundantExtensions` when this safe set was
    certified before, and remembers the *distinct* chosen probe sets behind each
    safe set so that the collisions (cause B) can be reported. -/
def recordExtension (s : Stats) (extension chosen : Array String) (worklist : String) : Stats :=
  let key := setKey extension
  let w : ExtensionWitness := { chosen, worklist }
  match s.extensionWitnesses[key]? with
  | none    =>
    { s with extensionWitnesses := s.extensionWitnesses.insert key #[w] }
  | some ws =>
    let chosenKey := setKey chosen
    let ws' := if ws.any (fun u => setKey u.chosen == chosenKey) then ws else ws.push w
    { s with redundantExtensions := s.redundantExtensions + 1
             extensionWitnesses  := s.extensionWitnesses.insert key ws' }

@[inline] def addSuccess (s : Stats) (free : Nat) : Stats :=
  { s with successMain  := s.successMain + 1
           freeWiresSum := s.freeWiresSum + free }

def avgFreeWires (s : Stats) : Float :=
  if s.successMain == 0 then 0.0
  else Float.ofNat s.freeWiresSum / Float.ofNat s.successMain

/-- Render the extension collisions: safe sets certified by ≥2 distinct chosen
    probe sets, with the producing probe set and worklist item for each.  Empty
    string when there are none. -/
def ppExtensionCollisions (s : Stats) : String :=
  let setStr (xs : List String) : String := "{" ++ String.intercalate ", " xs ++ "}"
  let collisions := s.extensionWitnesses.toList.filter (fun (_, ws) => ws.size >= 2)
  if collisions.isEmpty then ""
  else
    let body := collisions.map (fun (key, ws) =>
      let producers := ws.toList.map (fun w =>
        "      chosen " ++ setStr w.chosen.toList ++ "  from worklist [" ++ w.worklist ++ "]")
      "    extension " ++ setStr (key.splitOn "\n") ++ " (" ++ toString ws.size
        ++ " distinct probes):\n" ++ String.intercalate "\n" producers)
    "\n  extension collisions (" ++ toString collisions.length ++ "):\n"
      ++ String.intercalate "\n" body

def pp (s : Stats) : String :=
  s!"  total discharges       : {s.totalDischarges}\n  distinct probe sets    : {s.verdictCache.size}\n  repeated discharges    : {s.redundantUnionDischarges + s.redundantChosenDischarges}  (union {s.redundantUnionDischarges}, chosen {s.redundantChosenDischarges})\n  distinct extensions    : {s.extensionWitnesses.size}\n  repeated extensions    : {s.redundantExtensions}\n  successful main probes : {s.successMain}\n  free wires (sum)       : {s.freeWiresSum}\n  free wires (avg/main)  : {s.avgFreeWires}\n  anf fallbacks          : {s.anfFallbacks}" ++ s.ppExtensionCollisions

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
    (`checkProbeCompleteT`, simple + general rule) before declaring it insecure —
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
    let (g, sec) := checkProbeRoots g ids
    (g, (default : ProbeState), sec, stats.recordMiss key sec)

-- ============================================================
-- Chosen-probe construction and coupling discharge
-- ============================================================

/-- Build the chosen probe: the first `count` wires of each factor, in order.
    This is the size-`d` tuple actually discharged; the coupling extension then
    grows it into the certified-safe set (`couplingExtend`). -/
def buildProbeSimple (wl : ProbeWorklist) : Array String :=
  wl.foldl (fun acc f => acc ++ f.wires.extract 0 f.count) #[]

/-- Resolve candidate wires (those present in the DAG) to `(name, NodeId)` pairs
    for the coupling extension. -/
@[inline]
def candidatesOf (fw : HashMap String NodeId) (wires : Array String)
    : Array (String × NodeId) :=
  wires.filterMap (fun w => (fw[w]?).map (fun nid => (w, nid)))

/-- Discharge the `chosen` probe and return the coupling `T` that certified it.
    Mirrors `checkProbeByNames`'s discharge accounting (memo hit vs miss) so the
    `Stats` counts stay comparable, but always runs the engine: the extension
    needs `T`, which the verdict memo does not carry.  (Repeated `chosen`
    discharges are rare — bounded by `redundantExtensions` — so this costs little.)

    The coupling is derived by the **general substitution loop** (`checkProbeCompleteT`),
    matching `witness-replay`'s `rewriteWithWitness`, *not* the reference-counted
    fast path inside `checkProbeRoots` (which surfaces no coupling — its cascade
    steps are not tape relabels; see `applyRewrite`).  The reference-counted rule
    also records contexts from the original DAG and stops at the count invariant,
    producing an impoverished coupling that blinds far fewer wires; the
    substitution loop's coupling (contexts reflect each prior substitution)
    blinds strictly more.  It still lazily factors, so it certifies everything
    the fast path does (verdict unchanged), and factors only where the general
    rule stalls.

    `verdictCache` is shared with `checkProbeByNames`, whose entries come from
    the *tiered* engine.  The two are believed verdict-equivalent (the general
    loop subsumes the simple rule and factors on stall), but nothing proves it,
    so on a memo hit we cross-check: a disagreement means one engine has a
    soundness or completeness bug and must not be papered over. -/
def checkChosenCoupling (g : GlobalDAG) (fw : HashMap String NodeId)
    (stats : Stats) (names : Array String)
    : GlobalDAG × Bool × Array (NodeId × NodeId) × Stats :=
  let key := setKey names
  let ids := wireNamesToIds fw names
  let (g, sec, coupling) := checkProbeCompleteT g ids
  let stats := match stats.verdictCache[key]? with
    | some cached =>
      if cached != sec then
        panic! s!"checkChosenCoupling: engine disagreement on probe \
                  [{String.intercalate ", " (key.splitOn "\n")}]: \
                  tiered engine said secure={cached}, general loop says secure={sec}"
      else stats.recordHit .chosen
    | none   => stats.recordMiss key sec
  (g, sec, coupling, stats)

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
      -- Certify the representative tuple and capture its coupling `T`.
      let chosen := buildProbeSimple wl0
      let (g, chosenSec, coupling, stats) := checkChosenCoupling g fw stats chosen
      if !chosenSec then (g, stats, .Insecure chosen)
      else
        -- Grow the safe set: coupling extension (`extend`), or the naive baseline
        -- (`extend := false` — the chosen tuple covers only its own subsets).
        let (g, safe, anfCount) :=
          if extend then couplingExtend g coupling chosen (candidatesOf fw wires)
          else (g, chosen, 0)
        let stats := { stats with anfFallbacks := stats.anfFallbacks + anfCount }
        let free  := safe.size - chosen.size
        let stats := stats.addSuccess free
        let stats := stats.recordExtension safe chosen (ppWorklist wl0)
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
        let (g, chosenSec, coupling, stats) := checkChosenCoupling g fw stats chosen
        if !chosenSec then (g, stats, .Insecure chosen)
        else
          -- Grow the safe set: coupling extension (`extend`), or the naive baseline.
          let (g, safe, anfCount) :=
            if extend then couplingExtend g coupling chosen (candidatesOf fw allWires)
            else (g, chosen, 0)
          let stats := { stats with anfFallbacks := stats.anfFallbacks + anfCount }
          let free  := safe.size - chosen.size
          let stats := stats.addSuccess free
          let stats := stats.recordExtension safe chosen (ppWorklist wl)
          let safeSet : HashMap String Unit :=
            safe.foldl (fun m w => m.insert w ()) {}
          -- Vandermonde decomposition.  Split each factor's wires into its
          -- safe and unsafe parts, then enumerate the *product* over factors of
          -- every count distribution (`i` from safe, `count - i` from unsafe, for
          -- `i = 0 .. count`) — every cell except the all-safe one, whose tuples
          -- lie inside the already-certified safe set.
          let rec splitCells (g : GlobalDAG) (stats : Stats)
              (acc : ProbeWorklist) (idx : Nat) (allSafe : Bool)
              : GlobalDAG × Stats × CheckResult :=
            if idx >= wl.size then
              if allSafe then (g, stats, .Secure)        -- ⊆ safe set, already certified
              else checkAllMulti g fw stats acc extend
            else
              let f       := wl[idx]!
              let safeJ   := f.wires.filter (fun w => safeSet.contains w)
              let unsafeJ := f.wires.filter (fun w => !safeSet.contains w)
              let rec doI (g : GlobalDAG) (stats : Stats) (i : Nat)
                  : GlobalDAG × Stats × CheckResult :=
                let cell : ProbeWorklist :=
                  (if i == 0           then #[] else #[{ count := i,           wires := safeJ }]) ++
                  (if f.count - i == 0 then #[] else #[{ count := f.count - i, wires := unsafeJ }])
                let (g, stats, r) :=
                  splitCells g stats (acc ++ cell) (idx + 1) (allSafe && i == f.count)
                if !r.isSecure then (g, stats, r)
                else if i == 0 then (g, stats, .Secure)
                else doI g stats (i - 1)
              doI g stats f.count
          splitCells g stats #[] 0 true

end

-- ============================================================
-- Public entry point
-- ============================================================

/-- Verify `probingOrder`-probing security.  `extend := true` uses the coupling
    extension to grow each certified probe set into its safe set; `extend := false`
    is the naive baseline that performs no extension (each representative covers
    only its own subsets), degrading the space-split toward exhaustive enumeration.
    Both use the same sound rewrite checker, so the two verdicts must agree. -/
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

end verif
