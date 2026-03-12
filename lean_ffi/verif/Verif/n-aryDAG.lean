import Std.Data.HashMap

namespace verif

/-!
# Hash-Consed N-ary Circuit DAG with Multiplicative Factoring
-/

-- ============================================================
-- Base types
-- ============================================================

inductive VarType
  | Secret : String → VarType
  | Random : String → VarType
  | Public : String → VarType
  deriving Repr, DecidableEq, Hashable

abbrev NodeId := Nat

-- Single DAG node.
inductive NodeKind
  | xorNode  : Array NodeId → NodeKind  -- sorted; XOR-cancelled children (e + e = 0)
  | andNode  : Array NodeId → NodeKind  -- sorted; idempotent children    (e * e = e)
  | leaf     : VarType     → NodeKind
  | constVal : Bool        → NodeKind
  deriving Repr, DecidableEq, Hashable

-- ============================================================
-- DAG
-- ============================================================

open Std (HashMap)

-- Hash-consed boolean-circuit DAG.
structure DAG where
  nodes  : HashMap NodeId NodeKind  := {}
  intern : HashMap NodeKind NodeId  := {}
  nextId : NodeId                   := 0  -- Q: is it possible to determine IDs in a different way?

def empty : DAG := {}

namespace DAG

-- ============================================================
-- NodeID sorted array implementation
-- ============================================================

-- Returns the index of the first element >= val
@[inline]
def lowerBound (arr : Array NodeId) (val : NodeId) : Nat :=
  Id.run do
    let mut lo : Nat := 0
    let mut hi : Nat := arr.size
    while lo < hi do
      let mid := (lo + hi) >>> 1
      if arr[mid]! < val then lo := mid + 1 else hi := mid
    return lo

-- Tests membership
@[inline]
def sortedMem (arr : Array NodeId) (val : NodeId) : Bool :=
  let i := lowerBound arr val
  i < arr.size && arr[i]! == val

-- Inserts val into xorNode, incorporates cancellations when found
@[inline]
def xorInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr.eraseIdx! i
  else arr.insertIdx! i val

-- Inserts val into andNode, incorporates idempotency when found
@[inline]
def andInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr
  else arr.insertIdx! i val

-- ============================================================
-- Allocations with hash-consing
-- ============================================================

-- Looks up the structural kind of a node by its NodeId
@[inline]
def kind? (dag : DAG) (id : NodeId) : Option NodeKind :=
  dag.nodes.get? id

-- Allocates a new node k, without checking whether it is in intern (the caller should make sure that k is a new structure)
def alloc (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  let id := dag.nextId
  ({ dag with nodes  := dag.nodes.insert id k
              intern := dag.intern.insert k id
              nextId := id + 1 }, id)

-- Interns a new node k
@[inline]
def internNode (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  match dag.intern.get? k with
  | some id => (dag, id)
  | none    => dag.alloc k

-- ============================================================
-- Flattening
-- ============================================================

/-- Flattens an xorNode:
    - unpacks nested xorNode children
    - applies cancellations
    - returns a sorted xorNode
-/
private def flattenXor (dag : DAG) (ids : Array NodeId) : Array NodeId :=
  ids.foldl (fun acc id =>
    match dag.kind? id with
    | some (NodeKind.xorNode ch) => ch.foldl xorInsert acc
    | _                          => xorInsert acc id)
    #[]

/-- Flattens an andNode:
    - absorbs constVal = 1
    - annihilates constVal = 0
    - unpacks nested andNode children
    - returns a sorted andNode.
-/
private def flattenAnd (dag : DAG) (ids : Array NodeId) : Array NodeId × Bool :=
  ids.foldl (fun (acc, ann) id =>
    if ann then (acc, true)   -- already annihilated; skip remaining
    else match dag.kind? id with
    | some (NodeKind.constVal false) => (acc, true)
    | some (NodeKind.constVal true)  => (acc, ann)
    | some (NodeKind.andNode ch)     => (ch.foldl andInsert acc, ann)
    | _                              => (andInsert acc id, ann))
    (#[], false)

-- ============================================================
-- Smart constructors
-- ============================================================

def mkConst (dag : DAG) (b : Bool) : DAG × NodeId :=
  dag.internNode (NodeKind.constVal b)

def mkLeaf (dag : DAG) (v : VarType) : DAG × NodeId :=
  dag.internNode (NodeKind.leaf v)

/-- Build a canonical XOR node from a pre-normalised child array.
    Handles the identity collapses: ∅ → false, singleton → passthrough. -/
private def mkXorCanon (dag : DAG) (ch : Array NodeId) : DAG × NodeId :=
  match ch.size with
  | 0 => dag.mkConst false
  | 1 => (dag, ch[0]!)
  | _ => dag.internNode (NodeKind.xorNode ch)

/-- Build a canonical AND node from a pre-normalised child array.
    Handles annihilation and identity collapses. -/
private def mkAndCanon (dag : DAG) (ch : Array NodeId) (ann : Bool) : DAG × NodeId :=
  if ann then dag.mkConst false
  else match ch.size with
  | 0 => dag.mkConst true
  | 1 => (dag, ch[0]!)
  | _ => dag.internNode (NodeKind.andNode ch)

/-- Public XOR constructor: flattens nested XOR nodes and cancels duplicates
    before interning. The result is always in canonical form. -/
def mkXor (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  dag.mkXorCanon (dag.flattenXor ids)

/-- Public AND constructor: flattens nested AND nodes and deduplicates
    before interning. The result is always in canonical form. -/
def mkAnd (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  let (ch, ann) := dag.flattenAnd ids
  dag.mkAndCanon ch ann

-- ============================================================
-- Factoring algorithm
-- ============================================================

/-- Build a frequency map: for each `andNode` child of a XOR node, tally
    the number of AND-children that contain each individual factor. -/
private def factorFreqs (dag : DAG) (xorCh : Array NodeId) : HashMap NodeId Nat :=
  xorCh.foldl (fun freq id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) =>
      fac.foldl (fun m f => m.insert f ((m.get? f).getD 0 + 1)) freq
    | _ => freq)
    {}

/-- Return the factor appearing in the greatest number of AND-children,
    requiring a count of at least 2.
    Tie-break: prefer the smaller `NodeId` for determinism. -/
private def bestFactor (freq : HashMap NodeId Nat) : Option NodeId :=
  (freq.fold (fun best fac cnt =>
    if cnt < 2 then best
    else match best with
         | none          => some (fac, cnt)
         | some (bf, bc) =>
           if cnt > bc || (cnt == bc && fac < bf)
           then some (fac, cnt) else best)
    none).map (·.1)

/-- Remove `factor` from the AND-children of `id`, re-interning the result.
    If `factor` is not present, returns `id` unchanged. -/
private def stripFactor (dag : DAG) (id factor : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.andNode fac) =>
    let i := lowerBound fac factor
    if i < fac.size && fac[i]! == factor
    then dag.mkAndCanon (fac.eraseIdx! i) false
    else (dag, id)
  | _ => (dag, id)

/-- Apply one factoring step on a XOR-child array by factor `f`:
    1. Partition children into those whose AND-factors contain `f` and those
       that do not.
    2. Strip `f` from each term in the first partition.
    3. Build `f · (XOR of stripped terms)`.
    4. Rebuild the outer XOR as `(untouched terms) ⊕ (factored compound)`. -/
private def applyFactor (dag : DAG) (xorCh : Array NodeId) (f : NodeId) : DAG × NodeId :=
  let (withF, without) := xorCh.partition fun id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) => sortedMem fac f
    | _                   => false
  let (dag, stripped) :=
    withF.foldl (fun (d, acc) id =>
      let (d', s) := stripFactor d id f
      (d', acc.push s))
      (dag, #[])
  let (dag, innerXor) := dag.mkXor stripped
  let (dag, facTerm)  := dag.mkAnd #[f, innerXor]
  dag.mkXor (without.push facTerm)

/-- Fully factor the subgraph rooted at `id`, working bottom-up.

    - For XOR nodes: first recurse into all children, then greedily extract
      the most common multiplicative factor.  After rewriting, re-enter
      `factorNode` on the result so that newly introduced inner XOR nodes
      are also factored.
    - For AND nodes: recurse into children (they may contain inner XOR
      sub-expressions that benefit from factoring).
    - Leaves and constants: already fully factored; returned unchanged.

    Declared `partial` because the termination argument (strictly decreasing
    total factor-occurrence count) is non-trivial to encode as a Lean measure. -/
partial def factorNode (dag : DAG) (id : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.xorNode xorCh) =>
    -- Step 1: recurse bottom-up into children
    let (dag, xorCh') :=
      xorCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    -- Step 2: re-normalise after child updates (IDs may have changed)
    let (dag, id') := dag.mkXor xorCh'
    -- Step 3: greedy top-level factoring loop
    match dag.kind? id' with
    | some (NodeKind.xorNode ch) =>
      match bestFactor (factorFreqs dag ch) with
      | none   => (dag, id')       -- no common factor; fully factored
      | some f =>
        let (dag, id'') := applyFactor dag ch f
        factorNode dag id''        -- re-enter to handle newly created inner XORs
    | _ => (dag, id')

  | some (NodeKind.andNode andCh) =>
    -- Recurse into AND children (may wrap inner XOR sub-expressions)
    let (dag, andCh') :=
      andCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    dag.mkAnd andCh'

  | _ => (dag, id)   -- leaves and constants are fully factored

/-- Main entry point: fully factor the circuit node at `id`. -/
def factor (dag : DAG) (id : NodeId) : DAG × NodeId :=
  factorNode dag id

-- ============================================================
-- Debug pretty-printer
-- ============================================================

/-- Pretty-print a node and its entire subgraph for debugging.
    Declared `partial` due to DAG recursion. -/
partial def ppNode (dag : DAG) (id : NodeId) : String :=
  match dag.kind? id with
  | none                     => s!"[invalid:{id}]"
  | some (NodeKind.constVal true)    => "1"
  | some (NodeKind.constVal false)   => "0"
  | some (NodeKind.leaf (VarType.Secret s)) => s!"s({s})"
  | some (NodeKind.leaf (VarType.Random r)) => s!"r({r})"
  | some (NodeKind.leaf (VarType.Public p)) => p
  | some (NodeKind.xorNode ch)       =>
    "(" ++ String.intercalate " + " (ch.toList.map (ppNode dag)) ++ ")"
  | some (NodeKind.andNode ch)       =>
    "(" ++ String.intercalate " * " (ch.toList.map (ppNode dag)) ++ ")"

end DAG

-- ============================================================
-- Example
-- ============================================================

private def buildAndFactor : String :=
  let dag : DAG := {}
  let (dag, e) := dag.mkLeaf (VarType.Public "e")
  let (dag, a) := dag.mkLeaf (VarType.Public "a")
  let (dag, b) := dag.mkLeaf (VarType.Public "b")
  let (dag, c) := dag.mkLeaf (VarType.Public "c")
  let (dag, d) := dag.mkLeaf (VarType.Public "d")
  -- e·a
  let (dag, ea)   := dag.mkAnd #[e, a]
  -- b·c
  let (dag, bc)   := dag.mkAnd #[b, c]
  -- e·(b·c) — flattens to andNode{b, c, e}
  let (dag, ebc)  := dag.mkAnd #[e, bc]

  let (dag, ac)   := dag.mkXor #[a, c]

  let (dag, eac)  := dag.mkAnd #[e, ac]
  -- e·a ⊕ e·b·c ⊕ d
  let (dag, root) := dag.mkXor #[ea, ebc, d, eac]
  let (dag', fac) := dag.factor root
  s!"Before : {dag.ppNode root}\nAfter   : {dag'.ppNode fac}"

#eval buildAndFactor

end verif
