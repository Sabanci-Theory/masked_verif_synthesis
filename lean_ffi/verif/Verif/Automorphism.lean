import Verif.Circuit
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Circuit Automorphism Group (standalone experiment)

Computes the automorphism group of a `Circuit`, i.e. of the **netlist DAG**
(vertices = wires ∪ input shares ∪ leaves ∪ constants, edges = gate inputs).
This is the `netlist-syntactic` level of `.ai/AUTOMORPHISM_PLAN.md` §6.2 — the
conservative end of the hierarchy `netlist ⊂ DAG-canonical ⊂ ANF-exact ⊆ (★)`.
Anything it finds is a genuine probing automorphism (Def. 2 of the memo); it may
miss ones that only hold up to canonicalisation.

Not imported by `Verif.lean` (standalone for now):

    lake build Verif.Automorphism        -- typecheck
    lake env lean Verif/Automorphism.lean -- run the `#eval` demos at the bottom

## Algorithm

Individualisation–refinement, the standard partition-backtracking scheme (nauty /
saucy in miniature), specialised to a coloured DAG:

1. **Initial colouring** by vertex kind: body-XOR / body-AND / share-XOR /
   share-AND / Secret / Random / Public / const0 / const1.  Secrets, randoms and
   publics are *not* distinguished from one another — they are a priori
   interchangeable (memo §3: moving secrets is harmless).  Body wires and input
   shares *are* distinguished, since `φ` must map probe targets to probe targets.
2. **Refinement (1-WL)**: recolour each vertex by its own colour plus the
   multiset of its children's and parents' colours, to a fixed point.  Multiset
   invariance comes from summing hashed colours (wrapping `UInt64` addition), so
   a round is `O(V+E)`.  Parents are included because a random's role is
   determined by where it is *used*, which is what separates gadget randomness
   from encoding randomness.
3. **Search**: pick the smallest non-singleton cell, individualise a vertex on
   each side, refine, recurse.  Discrete-vs-discrete gives a candidate bijection.
4. **Exact verification** (`verifyMap`) of every candidate before it is returned:
   bijectivity, kind preservation, and children preserved as sorted multisets.
   Hash collisions in refinement can therefore only cost search time, never
   correctness — the trust boundary is `verifyMap`, nothing else.
5. **Group order and generators** by orbit–stabiliser: at each level the orbit of
   the anchor inside its cell times the order of its stabiliser.  Coset
   representatives plus stabiliser generators generate the whole group.

`searchBudget` bounds the number of search nodes; `Report.capped` says whether it
was hit (never silently truncate — memo §8.7).

## Two extras that make this usable for the memo's §11.1

* `contractAssoc` — the *relaxed* proposal graph.  A body wire used exactly once,
  whose sole user has the same operator, is an artefact of 2-ary decomposition
  (`addWireXorChain`); contracting it reconstructs the n-ary netlist the builder
  started from.  This is how the share symmetries become visible at all: on the
  honest netlist they are destroyed by the chain intermediates (memo §6.1).
* `stableDomain` — Definition 4.  Given leaf relabellings found on the relaxed
  graph, computes `D ⊆ wireOrder`, the wires whose image is again a wire, using
  the hash-consed DAG.  Wires outside `D` (the chain intermediates) simply drop
  out.  This is the "dispose" half of propose-and-dispose.
-/

-- ============================================================
-- Vertices and the netlist graph
-- ============================================================

inductive Vertex where
  | wire   : String  → Vertex
  | leaf   : VarType → Vertex
  | const  : Bool    → Vertex
  /-- Share-atomic mode only: one vertex per sharing, joined to all of its
      shares.  A graph automorphism must map bundle vertices to bundle vertices,
      which is exactly the fibring condition "the shares of `x` all land on the
      shares of one `y`" — enforced structurally, with no special-casing in the
      search. -/
  | bundle : String  → Vertex
  deriving Repr, DecidableEq, Hashable, Inhabited

def ppVertex : Vertex → String
  | Vertex.wire nm                  => nm
  | Vertex.leaf (VarType.Secret s)  => s
  | Vertex.leaf (VarType.Random r)  => r
  | Vertex.leaf (VarType.Public p)  => s!"p({p})"
  | Vertex.const b                  => if b then "1" else "0"
  | Vertex.bundle x                 => s!"[{x}]"

/-- The netlist as a coloured DAG.  `children` are sorted (gate inputs are
    unordered for XOR/AND, so they are compared as multisets); `parents` is the
    inverse relation, built once. -/
structure Graph where
  vertices : Array Vertex        := #[]
  children : Array (Array Nat)   := #[]
  parents  : Array (Array Nat)   := #[]
  /-- Hashed vertex-kind code; the initial colouring, and the invariant
      `verifyMap` checks. -/
  kind     : Array UInt64        := #[]
  index    : HashMap Vertex Nat  := {}
  deriving Inhabited

/-- splitmix64 finalizer.  Used to combine colours; every output bit depends on
    the whole input, so summing hashed child colours is a decent multiset
    invariant. -/
@[inline] def hash64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

def buildGraph (c : Circuit) : Graph := Id.run do
  let names := c.inputOrder ++ c.wireOrder
  -- wire vertices first, so their ids coincide with their position in `names`
  let mut vertices : Array Vertex := #[]
  let mut index : HashMap Vertex Nat := {}
  for nm in names do
    index := index.insert (Vertex.wire nm) vertices.size
    vertices := vertices.push (Vertex.wire nm)
  let mut children : Array (Array Nat) := Array.replicate vertices.size #[]
  for i in [0:names.size] do
    let nm := names[i]!
    let d  := c.wireDefs[nm]!
    let mut ch : Array Nat := #[]
    for inp in d.inputs do
      let v : Vertex := match inp with
        | WireInput.leaf l  => Vertex.leaf l
        | WireInput.const b => Vertex.const b
        | WireInput.wire w  => Vertex.wire w
      match index[v]? with
      | some id => ch := ch.push id
      | none    =>
        let id := vertices.size
        index    := index.insert v id
        vertices := vertices.push v
        children := children.push #[]
        ch := ch.push id
    children := children.set! i (ch.qsort (· < ·))
  -- parent adjacency
  let mut parents : Array (Array Nat) := Array.replicate vertices.size #[]
  for v in [0:children.size] do
    for ch in children[v]! do
      parents := parents.set! ch ((parents[ch]!).push v)
  -- kind colouring
  let isBody : HashMap String Unit := c.wireOrder.foldl (fun m w => m.insert w ()) {}
  let mut kind : Array UInt64 := Array.replicate vertices.size 0
  for v in [0:vertices.size] do
    let k : UInt64 := match vertices[v]! with
      | Vertex.wire nm =>
        let isX := (c.wireDefs[nm]!).isXor
        if isBody.contains nm then (if isX then 1 else 2) else (if isX then 3 else 4)
      | Vertex.leaf (VarType.Secret _) => 5
      | Vertex.leaf (VarType.Random _) => 6
      | Vertex.leaf (VarType.Public _) => 7
      | Vertex.const false             => 8
      | Vertex.const true              => 9
      | Vertex.bundle _                => 10
    kind := kind.set! v (hash64 k)
  return { vertices, children, parents, kind, index }

-- ============================================================
-- Colour refinement
-- ============================================================

/-- Tags keeping the child contribution distinguishable from the parent one. -/
private def childTag  : UInt64 := 0x51_7C_C1_B7_27_22_0A_95
private def parentTag : UInt64 := 0x2545F4914F6CDD1D

def refineStep (g : Graph) (col : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.replicate col.size 0
  for v in [0:col.size] do
    let mut acc := hash64 (col[v]! * 3 + 1)
    for c in g.children[v]! do
      acc := acc + hash64 (col[c]! ^^^ childTag)
    for p in g.parents[v]! do
      acc := acc + hash64 (col[p]! ^^^ parentTag)
    out := out.set! v (hash64 acc)
  return out

def distinctCount (col : Array UInt64) : Nat := Id.run do
  let sorted := col.qsort (· < ·)
  let mut n : Nat := 0
  let mut prev : Option UInt64 := none
  for c in sorted do
    if prev != some c then
      n := n + 1
      prev := some c
  return n

/-- Refine to a stable colouring: iterate until the partition stops getting
    finer.  Each round is `O(V+E)`; in practice 3–5 rounds suffice. -/
partial def refine (g : Graph) (col : Array UInt64) : Array UInt64 :=
  let col' := refineStep g col
  if distinctCount col' == distinctCount col then col' else refine g col'

/-- Cells of the colouring, as vertex-id arrays, grouped by colour. -/
def cellsOf (col : Array UInt64) : Array (Array Nat) := Id.run do
  let order := (Array.range col.size).qsort (fun a b =>
    col[a]! < col[b]! || (col[a]! == col[b]! && a < b))
  let mut cells : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[]
  for i in [0:order.size] do
    let v := order[i]!
    if cur.isEmpty || col[cur[0]!]! == col[v]! then
      cur := cur.push v
    else
      cells := cells.push cur
      cur := #[v]
  if !cur.isEmpty then cells := cells.push cur
  return cells

def smallestNonSingleton? (cells : Array (Array Nat)) : Option (Array Nat) :=
  cells.foldl (fun best c =>
    if c.size <= 1 then best
    else match best with
      | none   => some c
      | some b => if c.size < b.size then some c else best)
    none

/-- Give `v` a colour of its own, then let refinement propagate the split. -/
def individualize (col : Array UInt64) (v : Nat) : Array UInt64 :=
  col.set! v (hash64 (col[v]! * 0x9E3779B97F4A7C15 + 0x243F6A8885A308D3))

def sameColourMultiset (a b : Array UInt64) : Bool :=
  a.qsort (· < ·) == b.qsort (· < ·)

-- ============================================================
-- Exact verification — the trust boundary
-- ============================================================

/-- Is `m` a genuine automorphism of the netlist DAG?  Checks bijectivity, kind
    preservation (which subsumes body-wire / input-share / leaf-type
    preservation), and that children are preserved as multisets.  Everything
    upstream is a heuristic that only proposes candidates. -/
def verifyMap (g : Graph) (m : Array Nat) : Bool := Id.run do
  if m.size != g.vertices.size then return false
  let mut seen : Array Bool := Array.replicate m.size false
  for v in [0:m.size] do
    let i := m[v]!
    if i >= m.size then return false
    if seen[i]! then return false
    seen := seen.set! i true
  for v in [0:m.size] do
    if g.kind[v]! != g.kind[m[v]!]! then return false
    let img := (g.children[v]!.map (fun c => m[c]!)).qsort (· < ·)
    if img != g.children[m[v]!]! then return false
  return true

/-- Read the bijection off two discrete colourings. -/
def pairUp (cD cI : Array UInt64) : Option (Array Nat) := Id.run do
  let mut byColour : HashMap UInt64 Nat := {}
  for u in [0:cI.size] do
    byColour := byColour.insert cI[u]! u
  let mut m : Array Nat := Array.replicate cD.size 0
  for v in [0:cD.size] do
    match byColour[cD[v]!]? with
    | some u => m := m.set! v u
    | none   => return none
  return some m

-- ============================================================
-- Search
-- ============================================================

/-- Backtracking search for an automorphism carrying the individualisations of
    `colD` to those of `colI`.  Returns the remaining budget alongside the
    result, so the caller can report capping. -/
partial def searchMap (g : Graph) (fuel : Nat) (colD colI : Array UInt64)
    : Nat × Option (Array Nat) :=
  if fuel == 0 then (0, none)
  else
    let cD := refine g colD
    let cI := refine g colI
    if !sameColourMultiset cD cI then (fuel - 1, none)
    else
      match smallestNonSingleton? (cellsOf cD) with
      | none =>
        match pairUp cD cI with
        | some m => if verifyMap g m then (fuel - 1, some m) else (fuel - 1, none)
        | none   => (fuel - 1, none)
      | some cell =>
        let v      := cell[0]!
        let colVal := cD[v]!
        let cellI  := (Array.range g.vertices.size).filter (fun u => cI[u]! == colVal)
        Id.run do
          let mut f := fuel - 1
          for w in cellI do
            let (f', r) := searchMap g f (individualize cD v) (individualize cI w)
            f := f'
            match r with
            | some m => return (f, some m)
            | none   => pure ()
          return (f, none)

/-- Group order and generators, by orbit–stabiliser down a stabiliser chain.
    At each level: the orbit of the cell anchor `v` (its members are necessarily
    inside `v`'s cell, colours being automorphism-invariant), times the order of
    the stabiliser obtained by individualising `v`.  Returns
    `(remaining fuel, order, generators)`. -/
partial def groupOf (g : Graph) (fuel : Nat) (col : Array UInt64)
    : Nat × Nat × Array (Array Nat) :=
  if fuel == 0 then (0, 1, #[])
  else
    let c := refine g col
    match smallestNonSingleton? (cellsOf c) with
    | none      => (fuel, 1, #[])
    | some cell =>
      let v := cell[0]!
      Id.run do
        let mut f := fuel
        let mut gens : Array (Array Nat) := #[]
        let mut orbit : Nat := 1
        for w in cell do
          if w != v then
            let (f', r) := searchMap g f (individualize c v) (individualize c w)
            f := f'
            match r with
            | some m =>
              gens  := gens.push m
              orbit := orbit + 1
            | none => pure ()
        let (f'', ord, gens') := groupOf g f (individualize c v)
        return (f'', orbit * ord, gens ++ gens')

structure Report where
  /-- `|Aut|` of the coloured netlist DAG.  Exact unless `capped`. -/
  order  : Nat                  := 1
  gens   : Array (Array Nat)    := #[]
  /-- The search budget ran out; `order` is then a lower bound. -/
  capped : Bool                 := false
  deriving Inhabited

def automorphisms (c : Circuit) (searchBudget : Nat := 200000) : Graph × Report :=
  let g := buildGraph c
  let (fuel, ord, gens) := groupOf g searchBudget g.kind
  (g, { order := ord, gens := gens, capped := fuel == 0 })

-- ============================================================
-- Orbits and pretty printing
-- ============================================================

/-- Vertex orbits under the generators (union–find by repeated relabelling). -/
def orbitsOf (g : Graph) (gens : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let n := g.vertices.size
  let mut rep : Array Nat := Array.range n
  -- iterate to a fixed point: rep[v] := min over generators of rep[v], rep[m v]
  let mut changed := true
  while changed do
    changed := false
    for m in gens do
      for v in [0:n] do
        let a := rep[v]!
        let b := rep[m[v]!]!
        if a != b then
          let lo := if a < b then a else b
          rep := rep.set! v lo
          rep := rep.set! (m[v]!) lo
          changed := true
    -- path compression through the representative array
    for v in [0:n] do
      rep := rep.set! v rep[rep[v]!]!
  let mut buckets : HashMap Nat (Array Nat) := {}
  for v in [0:n] do
    buckets := buckets.insert rep[v]! (((buckets[rep[v]!]?).getD #[]).push v)
  let mut out : Array (Array Nat) := #[]
  for (_, b) in buckets.toList do
    if b.size > 1 then out := out.push b
  return out.qsort (fun a b => a[0]! < b[0]!)

def cyclesOf (m : Array Nat) : Array (Array Nat) := Id.run do
  let mut seen : Array Bool := Array.replicate m.size false
  let mut out : Array (Array Nat) := #[]
  for v in [0:m.size] do
    if !seen[v]! then
      let mut cyc : Array Nat := #[]
      let mut u := v
      while !seen[u]! do
        seen := seen.set! u true
        cyc  := cyc.push u
        u    := m[u]!
      if cyc.size > 1 then out := out.push cyc
  return out

def permOrder (m : Array Nat) : Nat :=
  (cyclesOf m).foldl (fun acc c => Nat.lcm acc c.size) 1

private def isLeafVertex : Vertex → Bool
  | Vertex.leaf _ => true
  | _             => false

/-- Cycle notation, truncated after `limit` cycles so a 30-cycle permutation of a
    big gadget stays readable.  `limit = 0` means no truncation. -/
private def ppCycles (g : Graph) (cycs : Array (Array Nat)) (limit : Nat) : String :=
  if cycs.isEmpty then "id"
  else
    let shown := if limit == 0 || cycs.size <= limit then cycs else cycs.extract 0 limit
    let body := String.intercalate " "
      (shown.toList.map (fun c =>
        "(" ++ String.intercalate " " (c.toList.map (fun v => ppVertex g.vertices[v]!)) ++ ")"))
    if shown.size == cycs.size then body
    else body ++ s!" … [{cycs.size - shown.size} more cycles of the same shape]"

/-- One generator, split into the leaf part `α` and the wire part `φ`
    (memo Def. 2), in cycle notation. -/
def ppAutomorphism (g : Graph) (m : Array Nat) (limit : Nat := 8) : String :=
  let cycs   := cyclesOf m
  let leaves := cycs.filter (fun c => isLeafVertex g.vertices[c[0]!]!)
  let wires  := cycs.filter (fun c => !isLeafVertex g.vertices[c[0]!]!)
  let moved  := cycs.foldl (fun acc c => acc + c.size) 0
  s!"    order {permOrder m}, moves {moved} vertices\n" ++
  s!"      α (leaves): {ppCycles g leaves limit}\n" ++
  s!"      φ (wires) : {ppCycles g wires limit}"

def ppReport (g : Graph) (r : Report) : String :=
  let cap := if r.capped then "  (BUDGET EXHAUSTED — lower bound only)" else ""
  let hdr :=
    s!"  |Aut| = {r.order}{cap}\n" ++
    s!"  vertices {g.vertices.size}, generators {r.gens.size}"
  if r.order == 1 then hdr ++ "\n  trivial group — no symmetry at this level."
  else
    let gens := String.intercalate "\n"
      (r.gens.toList.mapIdx (fun i m => s!"  generator {i}:\n" ++ ppAutomorphism g m))
    let orbs := orbitsOf g r.gens
    let shownOrbs := if orbs.size <= 12 then orbs else orbs.extract 0 12
    let orbStr := String.intercalate "\n"
      (shownOrbs.toList.map (fun o =>
        "    {" ++ String.intercalate ", " (o.toList.map (fun v => ppVertex g.vertices[v]!)) ++ "}"))
    let more := if orbs.size <= 12 then "" else s!"\n    … [{orbs.size - 12} more orbits]"
    hdr ++ "\n" ++ gens ++ s!"\n  non-trivial vertex orbits ({orbs.size}):\n" ++ orbStr ++ more

-- ============================================================
-- Relaxed proposal graph: contract 2-ary association chains
-- ============================================================

/-- Occurrence count of every wire name across all gate definitions. -/
private def useCounts (c : Circuit) : HashMap String Nat := Id.run do
  let mut m : HashMap String Nat := {}
  for nm in c.inputOrder ++ c.wireOrder do
    for inp in (c.wireDefs[nm]!).inputs do
      match inp with
      | WireInput.wire w => m := m.insert w ((m[w]?).getD 0 + 1)
      | _                => pure ()
  return m

/-- One contraction pass.  A **body** wire `u` that is used exactly once, whose
    sole user `p` has the same operator, is an artefact of 2-ary decomposition
    (`addWireXorChain` registers every prefix sum as a wire).  Inline `u` into
    `p` and drop it.

    The result is *not* a faithful netlist and must never be verified against —
    it is only the proposal graph of memo §6.5, used to make the share
    symmetries visible.  Verification happens in `stableDomain`. -/
def contractAssocStep (c : Circuit) : Circuit × Bool := Id.run do
  let uses := useCounts c
  let mut victim : Option (String × String) := none   -- (child, parent)
  for nm in c.wireOrder do
    if victim.isNone && (uses[nm]?).getD 0 == 1 then
      let d := c.wireDefs[nm]!
      -- find the unique user, and require the same operator
      for pn in c.inputOrder ++ c.wireOrder do
        if victim.isNone then
          let pd := c.wireDefs[pn]!
          if pd.isXor == d.isXor && pd.inputs.any (fun i => i == WireInput.wire nm) then
            victim := some (nm, pn)
  match victim with
  | none            => return (c, false)
  | some (nm, pn)   =>
    let d  := c.wireDefs[nm]!
    let pd := c.wireDefs[pn]!
    let newInputs :=
      (pd.inputs.filter (fun i => i != WireInput.wire nm)) ++ d.inputs
    let newDef := if pd.isXor then WireDef.xor newInputs else WireDef.and newInputs
    return ({ c with
      wireOrder := c.wireOrder.filter (· != nm)
      wireDefs  := (c.wireDefs.erase nm).insert pn newDef }, true)

/-- Contract association chains to a fixed point.  Returns the relaxed circuit
    and the names of the wires that were absorbed. -/
partial def contractAssoc (c : Circuit) : Circuit × Array String :=
  let before := c.wireOrder
  let rec go (c : Circuit) (fuel : Nat) : Circuit :=
    if fuel == 0 then c
    else match contractAssocStep c with
      | (c', true)  => go c' (fuel - 1)
      | (c', false) => c'
  let c' := go c (c.wireOrder.size + 1)
  let kept : HashMap String Unit := c'.wireOrder.foldl (fun m w => m.insert w ()) {}
  (c', before.filter (fun w => !kept.contains w))

-- ============================================================
-- Stable domain (memo Definition 4) — the "dispose" half
-- ============================================================

/-- Extract the leaf relabelling `α` of an automorphism. -/
def leafMapOf (g : Graph) (m : Array Nat) : HashMap VarType VarType := Id.run do
  let mut lm : HashMap VarType VarType := {}
  for v in [0:m.size] do
    match g.vertices[v]!, g.vertices[m[v]!]! with
    | Vertex.leaf a, Vertex.leaf b => lm := lm.insert a b
    | _, _ => pure ()
  return lm

/-- `α̂` on DAG nodes: permute leaves and rebuild through `mkXor`/`mkAnd`, so
    canonicalisation (XOR cancellation, AND idempotence, flattening) applies.
    By construction `⟦α̂ n⟧ = ⟦n⟧ ∘ α*`. -/
partial def permuteNode (g : GlobalDAG) (lm : HashMap VarType VarType)
    (memo : HashMap NodeId NodeId) (n : NodeId)
    : GlobalDAG × HashMap NodeId NodeId × NodeId :=
  match memo[n]? with
  | some m => (g, memo, m)
  | none   =>
    match g.dag.kind? n with
    | some (NodeKind.xorNode ch) =>
      let (g, memo, ch') := ch.foldl (fun (g, memo, acc) c =>
        let (g, memo, c') := permuteNode g lm memo c
        (g, memo, acc.push c')) (g, memo, #[])
      let (dag, m) := g.dag.mkXor ch'
      ({ g with dag }, memo.insert n m, m)
    | some (NodeKind.andNode ch) =>
      let (g, memo, ch') := ch.foldl (fun (g, memo, acc) c =>
        let (g, memo, c') := permuteNode g lm memo c
        (g, memo, acc.push c')) (g, memo, #[])
      let (dag, m) := g.dag.mkAnd ch'
      ({ g with dag }, memo.insert n m, m)
    | some (NodeKind.leaf v) =>
      match lm[v]? with
      | some v' =>
        let (dag, m) := g.dag.mkLeaf v'
        ({ g with dag }, memo.insert n m, m)
      | none    => (g, memo.insert n n, n)
    | _ => (g, memo.insert n n, n)

def invertLeafMap (lm : HashMap VarType VarType) : HashMap VarType VarType :=
  lm.fold (fun m a b => m.insert b a) {}

/-- **Definition 4.**  The largest `D ⊆ wireOrder` with `α̂(ν D) = ν D` for every
    `α` in the group generated by `leafMaps`.

    Testing the generators pointwise is **not** enough: a wire can survive every
    generator and still escape under a product, because the image wire need not
    itself be in `D`.  So this is a greatest-fixed-point computation — start from
    all wires and repeatedly drop any whose image under some generator is not the
    node of a wire *still in `D`* — and the generators' inverses are included so
    that stability is genuinely setwise.  On reaching the fixed point, `D` is
    stable under every generator, hence under the whole group.

    Wires outside `D` — the chain intermediates — drop out; that is expected, not
    a failure.  Membership is decided by interned `NodeId` equality on the
    hash-consed DAG, i.e. the `DAG-canonical` level of the §6.2 hierarchy, which
    is what admits the gadget *outputs* `s_i`. -/
def stableDomain (gd : GlobalDAG) (leafMaps : Array (HashMap VarType VarType))
    : GlobalDAG × Array String := Id.run do
  let wires := gd.circuit.wireOrder
  let maps  := leafMaps ++ leafMaps.map invertLeafMap
  -- Precompute every image once, sharing one `permuteNode` memo per map: the
  -- candidates in one circuit share almost all of their sub-DAG.
  let mut gd := gd
  let mut imgs : Array (Array NodeId) := Array.replicate wires.size #[]
  for lm in maps do
    let mut memo : HashMap NodeId NodeId := {}
    for i in [0:wires.size] do
      match gd.wires[wires[i]!]? with
      | none   => imgs := imgs.set! i ((imgs[i]!).push 0)
      | some n =>
        let (gd', memo', img) := permuteNode gd lm memo n
        gd := gd'
        memo := memo'
        imgs := imgs.set! i ((imgs[i]!).push img)
  -- Greatest fixed point.
  let mut inD : Array Bool := Array.replicate wires.size true
  let mut changed := true
  while changed do
    changed := false
    let mut nodesD : HashMap NodeId Unit := {}
    for i in [0:wires.size] do
      if inD[i]! then
        match gd.wires[wires[i]!]? with
        | some n => nodesD := nodesD.insert n ()
        | none   => pure ()
    for i in [0:wires.size] do
      if inD[i]! then
        if (imgs[i]!).any (fun img => !nodesD.contains img) then
          inD := inD.set! i false
          changed := true
  let mut keep : Array String := #[]
  for i in [0:wires.size] do
    if inD[i]! then keep := keep.push wires[i]!
  return (gd, keep)

-- ============================================================
-- Reporting entry points
-- ============================================================

/-- Analyse a circuit at the honest netlist level. -/
def analyse (name : String) (gd : GlobalDAG) (searchBudget : Nat := 200000) : String :=
  let (g, r) := automorphisms gd.circuit searchBudget
  s!"=== {name} — netlist automorphisms ===\n" ++ ppReport g r

/-- Analyse the relaxed (chain-contracted) circuit, then report which of the
    *original* wires survive as the stable domain `D`.  This is the propose-and-
    dispose pipeline of memo §6.5 in one call. -/
def analyseRelaxed (name : String) (gd : GlobalDAG) (searchBudget : Nat := 200000) : String :=
  let (rc, dropped) := contractAssoc gd.circuit
  let (g, r) := automorphisms rc searchBudget
  let head :=
    s!"=== {name} — relaxed (chain-contracted) automorphisms ===\n" ++
    s!"  contracted {dropped.size} association artefact(s): " ++
      "{" ++ String.intercalate ", " dropped.toList ++ "}\n" ++
    ppReport g r
  if r.order == 1 then head
  else
    let lms := r.gens.map (leafMapOf g)
    let (_, dom) := stableDomain gd lms
    let total := gd.circuit.wireOrder.size
    let outside := gd.circuit.wireOrder.filter (fun w => !dom.contains w)
    head ++ s!"\n  stable domain D: {dom.size}/{total} wires\n" ++
      "  outside D: {" ++ String.intercalate ", " outside.toList ++ "}"

-- ============================================================
-- SHARE-ATOMIC MODE
--
-- The leaf-level search above permutes DAG leaves, which caps share symmetry at
-- `(n-1)!`: with the canonical encoding, shares `0 … n-2` are bare random leaves
-- while share `n-1` is `x + Σ r`, so no leaf permutation can move the share that
-- carries the secret.  The 2-share DOM-AND is the minimal witness — it is rigid
-- at leaf level, yet swapping the two share *indices* is a genuine symmetry
-- (`u0↔u1`, `p01↔p10`, `c01↔c10`, `s0↔s1`).  On the leaves that map demands
-- `ra0 ↦ a + ra0`, an affine map, invisible to a graph search.
--
-- Treating input shares as ATOMS removes the cap: the object being permuted is
-- the share value, not the leaf encoding it, and the full `S_n` per sharing
-- becomes available.  The price is two side conditions that were free at leaf
-- level and must now be discharged mechanically:
--
--   (S1) each sharing's joint distribution is invariant under reordering its
--        shares.  True for the uniform XOR sharing, under all of `S_n`.
--   (S2) the body reaches the encoding only through the share values — no body
--        wire mentions an encoding random or a secret directly.  This must be
--        checked on `wireDefs`, NOT on the DAG: `mkXorCanon` on a one-element
--        list returns the child, so after interning `a0` *is* the leaf `ra0`.
--
-- Soundness of the transport theorem needs both.  Neither is implied by the
-- circuit; skipping them risks a false SECURE, not a lost opportunity.
-- ============================================================

/-- One input sharing, recovered from the netlist. -/
structure Sharing where
  secret  : String
  shares  : Array String
  randoms : Array String
  deriving Inhabited

/-- Outcome of the share-atomic preconditions. -/
structure ShareCheck where
  bundles  : Array Sharing := #[]
  problems : Array String  := #[]
  deriving Inhabited

def ShareCheck.ok (s : ShareCheck) : Bool := s.problems.isEmpty

private def leavesOfDef (c : Circuit) (nm : String) : Array VarType :=
  (c.wireDefs[nm]!).inputs.filterMap (fun i =>
    match i with | WireInput.leaf l => some l | _ => none)

private partial def ufFind (p : Array Nat) (i : Nat) : Nat :=
  if p[i]! == i then i else ufFind p p[i]!

/-- Recover the input sharings by grouping shares that share an encoding leaf.
    Two sharings that accidentally share randomness would merge into one bundle,
    which is itself a violation (the transport argument needs the sharings to be
    independent) and is reported. -/
def sharingsOf (c : Circuit) : ShareCheck := Id.run do
  let names := c.inputOrder
  let n := names.size
  let mut parent : Array Nat := Array.range n
  -- union shares that mention a common leaf
  let mut owner : HashMap VarType Nat := {}
  for i in [0:n] do
    for l in leavesOfDef c names[i]! do
      match owner[l]? with
      | none   => owner := owner.insert l i
      | some j =>
        let ri := ufFind parent i
        let rj := ufFind parent j
        if ri != rj then parent := parent.set! ri rj
  -- collect components
  let mut buckets : HashMap Nat (Array Nat) := {}
  for i in [0:n] do
    let r := ufFind parent i
    buckets := buckets.insert r (((buckets[r]?).getD #[]).push i)
  let mut out : Array Sharing := #[]
  let mut problems : Array String := #[]
  for (_, idxs) in buckets.toList do
    let shareNames := idxs.map (fun i => names[i]!)
    let mut secrets : Array String := #[]
    let mut randoms : Array String := #[]
    for i in idxs do
      for l in leavesOfDef c names[i]! do
        match l with
        | VarType.Secret s => if !secrets.contains s then secrets := secrets.push s
        | VarType.Random r => if !randoms.contains r then randoms := randoms.push r
        | VarType.Public _ => pure ()
    if secrets.size != 1 then
      problems := problems.push
        s!"sharing {shareNames.toList} carries {secrets.size} secrets ({secrets.toList}); \
           expected exactly one — sharings must be independent"
    else
      out := out.push { secret := secrets[0]!, shares := shareNames, randoms }
  return { bundles := out, problems }

/-- **(S1)** The canonical uniform XOR sharing: `n-1` shares are distinct fresh
    randoms, and one share is `secret + Σ` of exactly those randoms.  That
    distribution is invariant under every permutation of the shares, so the whole
    of `S_n` is available for this bundle. -/
def checkExchangeable (c : Circuit) (s : Sharing) : Bool := Id.run do
  if s.randoms.size + 1 != s.shares.size then return false
  let mut bare : Array String := #[]
  let mut carriers : Nat := 0
  for nm in s.shares do
    let d := c.wireDefs[nm]!
    if !d.isXor then return false
    let ls := leavesOfDef c nm
    if ls.size != d.inputs.size then return false        -- mentions a wire: not a plain sharing
    match ls.size with
    | 1 =>
      match ls[0]! with
      | VarType.Random r => if bare.contains r then return false else bare := bare.push r
      | _                => return false
    | _ =>
      -- the carrier: exactly the secret plus every encoding random, once each
      let mut sawSecret := false
      let mut rs : Array String := #[]
      for l in ls do
        match l with
        | VarType.Secret x => if x == s.secret && !sawSecret then sawSecret := true else return false
        | VarType.Random r => if rs.contains r then return false else rs := rs.push r
        | VarType.Public _ => return false
      if !sawSecret then return false
      if rs.size != s.randoms.size then return false
      for r in s.randoms do
        if !rs.contains r then return false
      carriers := carriers + 1
  return carriers == 1 && bare.size + 1 == s.shares.size

/-- **(S2)** No body wire mentions an encoding random or a secret directly. -/
def checkPrivateEncoding (c : Circuit) (bundles : Array Sharing) : Array String := Id.run do
  let mut encR : HashMap String Unit := {}
  for b in bundles do
    for r in b.randoms do encR := encR.insert r ()
  let mut problems : Array String := #[]
  for nm in c.wireOrder do
    for l in leavesOfDef c nm do
      match l with
      | VarType.Random r =>
        if encR.contains r then
          problems := problems.push s!"body wire '{nm}' uses encoding random '{r}' directly (S2)"
      | VarType.Secret x =>
        problems := problems.push s!"body wire '{nm}' uses secret '{x}' directly (S2)"
      | VarType.Public _ => pure ()
  return problems

/-- Run both preconditions. -/
def shareChecks (c : Circuit) : ShareCheck := Id.run do
  let base := sharingsOf c
  if !base.ok then return base
  let mut problems : Array String := checkPrivateEncoding c base.bundles
  for b in base.bundles do
    if !checkExchangeable c b then
      problems := problems.push
        s!"sharing of '{b.secret}' is not a uniform XOR sharing — reordering its \
           shares is not known to preserve its distribution (S1)"
  return { base with problems }

-- ------------------------------------------------------------
-- The share-atomic search graph
-- ------------------------------------------------------------

/-- Vertices: body wires, shares (childless atoms), gadget randoms, publics,
    constants, and one bundle vertex per sharing joined to its shares.  Secrets
    and encoding randoms do not appear at all — they live inside the abstraction.

    All shares carry the *same* colour, so any share may in principle map to any
    other; the bundle vertices are what restrict that to whole-sharing maps. -/
def buildShareGraph (c : Circuit) (bundles : Array Sharing) : Graph := Id.run do
  let mut vertices : Array Vertex := #[]
  let mut index : HashMap Vertex Nat := {}
  let mut children : Array (Array Nat) := #[]
  -- bundles first, then shares, then body wires
  for b in bundles do
    index := index.insert (Vertex.bundle b.secret) vertices.size
    vertices := vertices.push (Vertex.bundle b.secret)
    children := children.push #[]
  for nm in c.inputOrder do
    index := index.insert (Vertex.wire nm) vertices.size
    vertices := vertices.push (Vertex.wire nm)
    children := children.push #[]
  for nm in c.wireOrder do
    index := index.insert (Vertex.wire nm) vertices.size
    vertices := vertices.push (Vertex.wire nm)
    children := children.push #[]
  -- bundle → its shares
  for b in bundles do
    let bi := index[Vertex.bundle b.secret]!
    let mut ch : Array Nat := #[]
    for sh in b.shares do
      ch := ch.push index[Vertex.wire sh]!
    children := children.set! bi (ch.qsort (· < ·))
  -- body wire → its inputs
  for nm in c.wireOrder do
    let wi := index[Vertex.wire nm]!
    let mut ch : Array Nat := #[]
    for inp in (c.wireDefs[nm]!).inputs do
      let v : Vertex := match inp with
        | WireInput.leaf l  => Vertex.leaf l
        | WireInput.const b => Vertex.const b
        | WireInput.wire w  => Vertex.wire w
      match index[v]? with
      | some id => ch := ch.push id
      | none    =>
        let id := vertices.size
        index    := index.insert v id
        vertices := vertices.push v
        children := children.push #[]
        ch := ch.push id
    children := children.set! wi (ch.qsort (· < ·))
  -- parents
  let mut parents : Array (Array Nat) := Array.replicate vertices.size #[]
  for v in [0:children.size] do
    for ch in children[v]! do
      parents := parents.set! ch ((parents[ch]!).push v)
  -- colours
  let isBody : HashMap String Unit := c.wireOrder.foldl (fun m w => m.insert w ()) {}
  let mut kind : Array UInt64 := Array.replicate vertices.size 0
  for v in [0:vertices.size] do
    let k : UInt64 := match vertices[v]! with
      | Vertex.wire nm =>
        if isBody.contains nm then (if (c.wireDefs[nm]!).isXor then 1 else 2) else 3
      | Vertex.leaf (VarType.Random _) => 4
      | Vertex.leaf (VarType.Public _) => 5
      | Vertex.leaf (VarType.Secret _) => 6
      | Vertex.const false             => 7
      | Vertex.const true              => 8
      | Vertex.bundle _                => 9
    kind := kind.set! v (hash64 k)
  return { vertices, children, parents, kind, index }

-- ------------------------------------------------------------
-- The share-atomic DAG (shares as leaves) — for the exact domain check
-- ------------------------------------------------------------

/-- Rebuild the circuit into a DAG in which each input share is a *leaf* rather
    than its expansion.  A share permutation is then an ordinary leaf permutation
    of this DAG, so `permuteNode` and `stableDomain` apply verbatim — and
    `mkXor`'s flattening still admits the gadget outputs whose `WireDef` mentions
    a contracted intermediate. -/
def buildAtomicDAG (c : Circuit) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := { circuit := c }
  for nm in c.inputOrder do
    let (dag, id) := g.dag.mkLeaf (VarType.Public s!"sh:{nm}")
    g := { g with dag := dag, wires := g.wires.insert nm id }
  for nm in c.wireOrder do
    let d := c.wireDefs[nm]!
    let mut ids : Array NodeId := #[]
    for inp in d.inputs do
      match inp with
      | WireInput.wire w  => ids := ids.push (g.wires[w]!)
      | WireInput.leaf l  =>
        let (dag, id) := g.dag.mkLeaf l
        g := { g with dag }
        ids := ids.push id
      | WireInput.const b =>
        let (dag, id) := g.dag.mkConst b
        g := { g with dag }
        ids := ids.push id
    let (dag, nid) := if d.isXor then g.dag.mkXor ids else g.dag.mkAnd ids
    g := { g with dag := dag, wires := g.wires.insert nm nid }
  return g

/-- Leaf relabelling induced by a share-graph automorphism: shares map through
    their `sh:` atoms, gadget randoms and publics map as themselves. -/
def atomicLeafMap (g : Graph) (m : Array Nat) : HashMap VarType VarType := Id.run do
  let mut lm : HashMap VarType VarType := {}
  for v in [0:m.size] do
    match g.vertices[v]!, g.vertices[m[v]!]! with
    | Vertex.wire a, Vertex.wire b =>
      lm := lm.insert (VarType.Public s!"sh:{a}") (VarType.Public s!"sh:{b}")
    | Vertex.leaf a, Vertex.leaf b => lm := lm.insert a b
    | _, _ => pure ()
  return lm

-- ------------------------------------------------------------
-- Entry point
-- ------------------------------------------------------------

/-- Analyse a circuit with input shares treated as atoms.  `relax := true` also
    contracts association chains first (§6.1 of the plan: the chain obstruction
    is orthogonal to how shares are encoded, so the two repairs compose). -/
def analyseShares (name : String) (gd : GlobalDAG) (relax : Bool := false)
    (searchBudget : Nat := 200000) : String :=
  let c0 := gd.circuit
  let chk := shareChecks c0
  let relaxTag := if relax then " (relaxed)" else ""
  let head := s!"=== {name} — share-atomic automorphisms{relaxTag} ===\n"
  if !chk.ok then
    head ++ "  PRECONDITIONS FAILED — share-atomic mode refused:\n" ++
      String.intercalate "\n" (chk.problems.toList.map (fun p => "    ✗ " ++ p))
  else
    let bundleLine :=
      "  sharings: " ++ String.intercalate ", "
        (chk.bundles.toList.map (fun b => s!"{b.secret}⟨{b.shares.size}⟩")) ++
      "   (S1) uniform XOR ✓   (S2) encoding private ✓\n"
    let (c, dropped) := if relax then contractAssoc c0 else (c0, #[])
    -- the bundles must be re-derived against the possibly-contracted circuit
    let chk2 := shareChecks c
    let bundles := if chk2.ok then chk2.bundles else chk.bundles
    let g := buildShareGraph c bundles
    let (fuel, ord, gens) := groupOf g searchBudget g.kind
    let r : Report := { order := ord, gens := gens, capped := fuel == 0 }
    let dropLine :=
      if relax then s!"  contracted {dropped.size} association artefact(s)\n" else ""
    let body := head ++ bundleLine ++ dropLine ++ ppReport g r
    if r.order == 1 then body
    else
      let atomic := buildAtomicDAG c0
      let (_, dom) := stableDomain atomic (r.gens.map (atomicLeafMap g))
      let total := c0.wireOrder.size
      let outside := c0.wireOrder.filter (fun w => !dom.contains w)
      body ++ s!"\n  stable domain D: {dom.size}/{total} wires\n" ++
        "  outside D: {" ++ String.intercalate ", " outside.toList ++ "}"

-- ============================================================
-- Demo circuits (local copies mirroring `Main.lean`, so this file stands alone)
-- ============================================================

partial def demoXorChain (g : GlobalDAG) (out : String) (terms : Array WireInput) : GlobalDAG :=
  if terms.size == 0 then g.addWireXor out #[WireInput.const false]
  else if terms.size == 1 then g.addWireXor out #[terms[0]!]
  else
    let firstName := if terms.size == 2 then out else s!"{out}m0"
    let g := g.addWireXor firstName #[terms[0]!, terms[1]!]
    let rec go (g : GlobalDAG) (acc : String) (idx : Nat) : GlobalDAG :=
      if idx >= terms.size then g
      else
        let name := if idx + 1 == terms.size then out else s!"{out}m{idx - 1}"
        go (g.addWireXor name #[WireInput.wire acc, terms[idx]!]) name (idx + 1)
    go g firstName 2

def demoShares (g : GlobalDAG) (pre sec : String) (shares : Nat) : GlobalDAG := Id.run do
  let mut g := g
  let mut last : Array WireInput := #[WireInput.leaf (VarType.Secret sec)]
  for i in [0:shares-1] do
    g := g.addShare s!"{pre}{i}" #[WireInput.leaf (VarType.Random s!"r{pre}{i}")]
    last := last.push (WireInput.leaf (VarType.Random s!"r{pre}{i}"))
  g := g.addShare s!"{pre}{shares-1}" last
  return g

/-- DOM-independent AND, `shares` shares.  Mirrors `Main.lean`'s `domAND`. -/
def demoDomAND (shares : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for (pre, sec) in #[("a", "a"), ("b", "b")] do
    g := demoShares g pre sec shares
  for i in [0:shares] do
    g := g.addWireAnd s!"u{i}" #[WireInput.wire s!"a{i}", WireInput.wire s!"b{i}"]
  for i in [0:shares] do
    for j in [i+1:shares] do
      g := g.addWireAnd s!"p{i}{j}" #[WireInput.wire s!"a{i}", WireInput.wire s!"b{j}"]
      g := g.addWireAnd s!"p{j}{i}" #[WireInput.wire s!"a{j}", WireInput.wire s!"b{i}"]
  for i in [0:shares] do
    for j in [i+1:shares] do
      let r := WireInput.leaf (VarType.Random s!"r{i}{j}")
      g := g.addWireXor s!"c{i}{j}" #[WireInput.wire s!"p{i}{j}", r]
      g := g.addWireXor s!"c{j}{i}" #[WireInput.wire s!"p{j}{i}", r]
  for i in [0:shares] do
    let mut terms : Array WireInput := #[WireInput.wire s!"u{i}"]
    for j in [0:shares] do
      if j != i then terms := terms.push (WireInput.wire s!"c{i}{j}")
    g := demoXorChain g s!"s{i}" terms
  return g

/-- DOM Keccak χ, `shares` shares.  Mirrors `Main.lean`'s `domKeccakChi`.
    Expected to carry the `C₅` bit rotation (memo §6.3). -/
def demoKeccakChi (shares : Nat) : GlobalDAG := Id.run do
  let names := #["a", "b", "c", "d", "e"]
  let mut g : GlobalDAG := {}
  for v in names do
    g := demoShares g v v shares
  for k in [0:5] do
    let x := names[k]!
    let y := names[(k+1) % 5]!
    let z := names[(k+2) % 5]!
    g := g.addWireXor s!"n{k}" #[WireInput.wire s!"{y}0", WireInput.const true]
    let ys := fun (i : Nat) => if i == 0 then s!"n{k}" else s!"{y}{i}"
    for i in [0:shares] do
      for j in [0:shares] do
        g := g.addWireAnd s!"q{k}_{i}{j}" #[WireInput.wire (ys i), WireInput.wire s!"{z}{j}"]
    for i in [0:shares] do
      for j in [0:shares] do
        if i != j then
          let p := min i j
          let q := max i j
          g := g.addWireXor s!"t{k}_{i}{j}"
            #[WireInput.wire s!"q{k}_{i}{j}", WireInput.leaf (VarType.Random s!"r{k}_{p}{q}")]
    for i in [0:shares] do
      let mut terms : Array WireInput := #[WireInput.wire s!"q{k}_{i}{i}"]
      for j in [0:shares] do
        if j != i then terms := terms.push (WireInput.wire s!"t{k}_{i}{j}")
      g := demoXorChain g s!"s{k}_{i}" terms
      g := g.addWireXor s!"f{k}_{i}" #[WireInput.wire s!"{x}{i}", WireInput.wire s!"s{k}_{i}"]
  return g

/-- The `ℤ₃` counterexample of memo Theorem 3: `w_i = s + r_i + r_{i+1}`.
    Every pair is secure, the triple leaks `s`.  Should have a `C₃` symmetry. -/
def demoZ3 : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  for i in [0:3] do
    let j := (i + 1) % 3
    g := g.addWireXor s!"h{i}"
      #[WireInput.leaf (VarType.Secret "s"), WireInput.leaf (VarType.Random s!"r{i}")]
    g := g.addWireXor s!"w{i}"
      #[WireInput.wire s!"h{i}", WireInput.leaf (VarType.Random s!"r{j}")]
  return g

/-- Run one analysis and time it. -/
def timed (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let s := f ()
  let t1 ← IO.monoMsNow
  IO.println s
  IO.println s!"  [{t1 - t0} ms]"
  IO.println ""

def runDemo : IO Unit := do
  -- the minimal witness that the two tiers differ
  timed (fun _ => analyse       "domAND 2"       (demoDomAND 2))
  timed (fun _ => analyseShares "domAND 2"       (demoDomAND 2))
  -- leaf tier vs share tier, with and without chain contraction
  timed (fun _ => analyseShares "domAND 3"       (demoDomAND 3))
  timed (fun _ => analyseShares "domAND 3"       (demoDomAND 3) true)
  timed (fun _ => analyseShares "domAND 5"       (demoDomAND 5) true)
  timed (fun _ => analyse       "domKeccakChi 2" (demoKeccakChi 2))
  timed (fun _ => analyseShares "domKeccakChi 2" (demoKeccakChi 2))
  timed (fun _ => analyseShares "domKeccakChi 3" (demoKeccakChi 3) true)

#eval runDemo

end verif
