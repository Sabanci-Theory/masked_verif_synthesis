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

/-- Single DAG node. -/
inductive NodeKind
  | xorNode  : Array NodeId → NodeKind  -- sorted; XOR-cancelled children (e + e = 0)
  | andNode  : Array NodeId → NodeKind  -- sorted; idempotent children    (e * e = e)
  | leaf     : VarType      → NodeKind
  | constVal : Bool         → NodeKind
  deriving Repr, DecidableEq, Hashable

-- ============================================================
-- DAG
-- ============================================================

open Std (HashMap)

/-- A hash-consed `𝔽₂`-circuit DAG.
    `∀id : NodeId, intern[nodes[id]] = id ∧ ∀k : NodeKind, nodes[intern[k]] = k`. -/
structure DAG where
  nodes  : HashMap NodeId NodeKind := {}
  intern : HashMap NodeKind NodeId := {}
  nextId : NodeId                  := 0  -- Q: is it possible to determine IDs in a different way?
  randoms : Array NodeId           := #[]
  secrets : Array NodeId           := #[]

namespace DAG

-- ============================================================
-- NodeID sorted array helpers
-- ============================================================

/-- Returns the index of the first element `≥ val` . -/
@[inline]
def lowerBound (arr : Array NodeId) (val : NodeId) : Nat :=
  Id.run do
    let mut lo : Nat := 0
    let mut hi : Nat := arr.size
    while lo < hi do
      let mid := (lo + hi) >>> 1
      if arr[mid]! < val then lo := mid + 1 else hi := mid
    return lo

/-- Tests whether `val` is in `arr`. -/
@[inline]
def sortedMem (arr : Array NodeId) (val : NodeId) : Bool :=
  let i := lowerBound arr val
  i < arr.size && arr[i]! == val

/-- Inserts into an xorNode, the value `val`.
    If `val` is already present, the function cancels it, otherwise it inserts it in the sorted position.
    Maintains the "sorted, no-duplicate" specification for xorNode. -/
@[inline]
def xorInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr.eraseIdx! i
  else arr.insertIdx! i val

/-- Inserts into an andNode, the value `val`.
    If `val` is already present, the function skips its insertion, otherwise it inserts it in the sorted position.
    Maintains the "sorted, no-duplicate" specification for andNode. -/
@[inline]
def andInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr
  else arr.insertIdx! i val

-- ============================================================
-- Allocations with hash-consing
-- ============================================================

/-- Looks up the structural kind of a node by its `NodeId`. -/
@[inline]
def kind? (dag : DAG) (id : NodeId) : Option NodeKind :=
  dag.nodes[id]?

/-- Allocates a new node `k`, without checking whether it is in intern (the caller should make sure that `k` is a new structure). -/
def alloc (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  let id := dag.nextId
  ({ dag with nodes  := dag.nodes.insert id k
              intern := dag.intern.insert k id
              nextId := id + 1 }, id)

/-- Returns the existing `NodeId` for `k` if already interned, or allocate a fresh node and return its id. -/
@[inline]
def internNode (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  match dag.intern[k]? with
  | some id => (dag, id)
  | none    => dag.alloc k

@[inline]
def isSecretNode (dag : DAG) (id : NodeId) : Bool :=
  match dag.kind? id with
  | some (NodeKind.leaf (VarType.Secret _)) => true
  | _                                       => false


-- ============================================================
-- Flattening
-- ============================================================

/-- Flattens an xorNode:
    - unpacks nested xorNode children
    - applies cancellations
    - returns a sorted xorNode -/
def flattenXor (dag : DAG) (ids : Array NodeId) : Array NodeId :=
  ids.foldl (fun acc id =>
    match dag.kind? id with
    | some (NodeKind.xorNode ch) => ch.foldl xorInsert acc -- It unpacks xorNodes that are only one level deeper
    | _                          => xorInsert acc id)
    #[]

/-- Flattens an andNode:
    - absorbs constVal = 1
    - annihilates constVal = 0
    - unpacks nested andNode children
    - returns a sorted andNode and a Bool value to signal whether the product vanished -/
def flattenAnd (dag : DAG) (ids : Array NodeId) : Array NodeId × Bool :=
  ids.foldl (fun (acc, ann) id =>
    if ann then (acc, true)   -- already annihilated; skip remaining
    else match dag.kind? id with
    | some (NodeKind.constVal false) => (acc, true)
    | some (NodeKind.constVal true)  => (acc, ann)
    | some (NodeKind.andNode ch)     => (ch.foldl andInsert acc, ann) -- It unpacks andNodes that are only one level deeper
    | _                              => (andInsert acc id, ann))
    (#[], false)

-- ============================================================
-- Smart constructors
-- ============================================================

def mkConst (dag : DAG) (b : Bool) : DAG × NodeId :=
  dag.internNode (NodeKind.constVal b)

def mkLeaf (dag : DAG) (v : VarType) : DAG × NodeId :=
  let k := NodeKind.leaf v
  match dag.intern[k]? with
  | some id => (dag, id)
  | none    =>
    let (dag', id) := dag.alloc k
    match v with
    | VarType.Random _ => ({ dag' with randoms := dag'.randoms.push id }, id)
    | VarType.Secret _ => ({ dag' with secrets := dag'.secrets.push id }, id)
    | _                => (dag', id)

/-- Builds a canonical XOR node from a pre-normalised child array.
    Handles the identity collapses: Array.empty → false, singleton → passthrough. -/
def mkXorCanon (dag : DAG) (ch : Array NodeId) : DAG × NodeId :=
  match ch.size with
  | 0 => dag.mkConst false -- something stupid; not to be reached
  | 1 => (dag, ch[0]!)     -- might be reached from `applyFactor`
  | _ => dag.internNode (NodeKind.xorNode ch)

/-- Builds a canonical AND node from a pre-normalised child array.
    Handles annihilation and identity collapses. -/
def mkAndCanon (dag : DAG) (ch : Array NodeId) (ann : Bool) : DAG × NodeId :=
  if ann then dag.mkConst false
  else match ch.size with
  | 0 => dag.mkConst true -- something stupid; not to be reached
  | 1 => (dag, ch[0]!)    -- might be reached from `stripFactor`
  | _ => dag.internNode (NodeKind.andNode ch)

/-- Public XOR constructor: flattens nested XOR nodes and cancels duplicates
    before interning. The result is always in canonical form. -/
def mkXor (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  dag.mkXorCanon (dag.flattenXor ids)

/-- Public AND constructor: flattens nested AND nodes and cancels duplicates
    before interning. The result is always in canonical form. -/
def mkAnd (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  let (ch, ann) := dag.flattenAnd ids
  dag.mkAndCanon ch ann

-- ============================================================
-- Factoring algorithm
-- ============================================================

/-- Builds a frequency map: for each `andNode` child of a XOR node, count
    the number of AND-children that contain each individual factor. -/
def factorFreqs (dag : DAG) (xorCh : Array NodeId) : HashMap NodeId Nat :=
  xorCh.foldl (fun freq id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) =>
      fac.foldl (fun m f => m.insert f (m[f]?.getD 0 + 1)) freq
    | _ => freq)
    {}

/-- Returns the factor appearing in the greatest number of AND-children, requiring a count of at least 2.
    In case of tie, it prefers the smaller `NodeId` for determinism. -/
def bestFactor (freq : HashMap NodeId Nat) : Option NodeId :=
  (freq.fold (fun best fac cnt =>
    if cnt < 2 then best
    else match best with
         | none          => some (fac, cnt)
         | some (bf, bc) => if cnt > bc || (cnt == bc && fac < bf)
                            then some (fac, cnt)
                            else best)
    none).map (·.fst)

/-- Removes `factor` from the AND-children of `id`, re-interning the result.
    If `factor` is not present, returns `id` unchanged. -/
def stripFactor (dag : DAG) (id factor : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.andNode fac) =>
    let i := lowerBound fac factor
    if i < fac.size && fac[i]! == factor
    then dag.mkAndCanon (fac.eraseIdx! i) false -- If the term `factor` need be removed from the andNode `fac`, a new
                                                -- AND-node is created with exactly the same content, except `factor`.
    else (dag, id)
  | _ => (dag, id)

/-- Applies one factoring step on a XOR-child array by factor `f`:
    1. Partitions children into those whose AND-factors contain `f` and those that do not.
    2. Strips `f` from each term in the first partition.
    3. Builds `f * (XOR of stripped terms)`.
    4. Rebuilds the outer XOR as `(untouched terms) + (factored compound)`. -/
def applyFactor (dag : DAG) (xorCh : Array NodeId) (f : NodeId) : DAG × NodeId :=
  let (withF, without) := xorCh.partition (fun id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) => sortedMem fac f
    | _                           => false)
  let (dag, stripped) := withF.foldl (fun (d, acc) id =>
    let (d', s) := stripFactor d id f
    (d', acc.push s))
    (dag, #[])
  let (dag, innerXor) := dag.mkXor stripped
  let (dag, facTerm)  := dag.mkAnd #[f, innerXor]
  dag.mkXor (without.push facTerm)

/-- Fully factors the subgraph rooted at `id`, working bottom-up.
    - For XOR nodes: first recurse into all children, then greedily extract
      the most common multiplicative factor.  After rewriting, re-enter
      `factorNode` on the result so that newly introduced inner XOR nodes
      are also factored.
    - For AND nodes: recurse into children (they may contain inner XOR
      sub-expressions that benefit from factoring).
    - Leaves and constants: already fully factored; returned unchanged.

    TODO: Declared `partial` because the termination argument (strictly decreasing
    total factor-occurrence count) is non-trivial to prove. -/
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
    -- Step 3: top-level factoring loop
    match dag.kind? id' with
    | some (NodeKind.xorNode ch) =>
      match bestFactor (factorFreqs dag ch) with
      | none   => (dag, id')       -- no common factor; fully factored
      | some f =>
        let (dag, id'') := applyFactor dag ch f
        factorNode dag id''        -- re-enter to handle newly created inner XORs
    | _ => (dag, id')              -- unreachable

  | some (NodeKind.andNode andCh) =>
    -- Recurse into AND children (may wrap inner XOR sub-expressions)
    let (dag, andCh') :=
      andCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    dag.mkAnd andCh'

  | _ => (dag, id)   -- leaves and constants are already fully factored

/-- Main entry point for the factoring algorithm: fully factor the circuit from nodes at `ids`. -/
def factor (dag : DAG) (ids : Array NodeId) : DAG × Array NodeId :=
  ids.foldl (fun (d, roots) id =>
              let (d', id') := d.factorNode id
              (d', roots.push id'))
            (dag, #[])

-- ============================================================
-- Debug pretty-printer
-- ============================================================

/-- Pretty-prints a node and its entire subgraph for debugging.
    Declared `partial` due to DAG recursion. -/
partial def ppNode (dag : DAG) (id : NodeId) : String :=
  match dag.kind? id with
  | none                     => s!"[invalid:{id}]"
  | some (NodeKind.constVal true)    => "1"
  | some (NodeKind.constVal false)   => "0"
  | some (NodeKind.leaf (VarType.Secret s)) => s
  | some (NodeKind.leaf (VarType.Random r)) => r
  | some (NodeKind.leaf (VarType.Public p)) => s!"p({p})"
  | some (NodeKind.xorNode ch)       =>
    "(" ++ String.intercalate " + " (ch.toList.map (ppNode dag)) ++ ")"
  | some (NodeKind.andNode ch)       =>
    "(" ++ String.intercalate " * " (ch.toList.map (ppNode dag)) ++ ")"

end DAG

-- ============================================================
-- Example
-- ============================================================

def example0 : IO Unit :=
  let dag : DAG := {}
  let (dag, e)  := dag.mkLeaf (VarType.Public "e")
  let (dag, a)  := dag.mkLeaf (VarType.Secret "a")
  let (dag, b)  := dag.mkLeaf (VarType.Secret "b")
  let (dag, r0) := dag.mkLeaf (VarType.Random "r0")
  let (dag, d)  := dag.mkLeaf (VarType.Public "d")

  let (dag, ea) := dag.mkAnd #[e, a]

  let (dag, br0)  := dag.mkAnd #[b, r0]
  let (dag, ebr0) := dag.mkAnd #[e, br0]

  let (dag, ar0)  := dag.mkXor #[a, r0]
  let (dag, w)    := dag.mkXor #[r0, a, a, a]
  let (dag, ear0) := dag.mkAnd #[e, ar0]

  let (dag, root) := dag.mkXor #[ea, ebr0, d, ear0]
  let (dag', fac) := dag.factor #[root]
  IO.println s!"{dag.ppNode root}\n{dag'.ppNode fac[0]!}\n{w == ar0}"

#eval example0

end verif
