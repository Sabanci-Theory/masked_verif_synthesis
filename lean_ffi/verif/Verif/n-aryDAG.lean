import Std.Data.HashMap

namespace verif

open Std (HashMap)

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
  deriving Repr, DecidableEq, Hashable, Inhabited

abbrev NodeId := Nat

/-- Single DAG node. -/
inductive NodeKind
  | xorNode  : Array NodeId → NodeKind
  | andNode  : Array NodeId → NodeKind
  | leaf     : VarType      → NodeKind
  | constVal : Bool         → NodeKind
  deriving Repr, DecidableEq, Hashable, Inhabited

-- ============================================================
-- DAG
-- ============================================================

/-- A hash-consed 𝔽₂-circuit DAG. -/
structure DAG where
  nodes   : HashMap NodeId NodeKind := {}
  intern  : HashMap NodeKind NodeId := {}
  nextId  : NodeId                  := 0
  randoms : Array NodeId            := #[]
  secrets : Array NodeId            := #[]
  deriving Inhabited

namespace DAG

-- sorted-array helpers

@[inline]
def lowerBound (arr : Array NodeId) (val : NodeId) : Nat :=
  Id.run do
    let mut lo : Nat := 0
    let mut hi : Nat := arr.size
    while lo < hi do
      let mid := (lo + hi) >>> 1
      if arr[mid]! < val then lo := mid + 1 else hi := mid
    return lo

@[inline]
def sortedMem (arr : Array NodeId) (val : NodeId) : Bool :=
  let i := lowerBound arr val
  i < arr.size && arr[i]! == val

@[inline]
def xorInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr.eraseIdx! i
  else arr.insertIdx! i val

@[inline]
def andInsert (arr : Array NodeId) (val : NodeId) : Array NodeId :=
  let i := lowerBound arr val
  if i < arr.size && arr[i]! == val then arr
  else arr.insertIdx! i val

-- allocation / interning

@[inline]
def kind? (dag : DAG) (id : NodeId) : Option NodeKind :=
  dag.nodes[id]?

def alloc (dag : DAG) (k : NodeKind) : DAG × NodeId :=
  let id := dag.nextId
  ({ dag with nodes  := dag.nodes.insert id k
              intern := dag.intern.insert k id
              nextId := id + 1 }, id)

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

-- flattening

def flattenXor (dag : DAG) (ids : Array NodeId) : Array NodeId :=
  ids.foldl (fun acc id =>
    match dag.kind? id with
    | some (NodeKind.xorNode ch) => ch.foldl xorInsert acc
    | _                          => xorInsert acc id)
    #[]

def flattenAnd (dag : DAG) (ids : Array NodeId) : Array NodeId × Bool :=
  ids.foldl (fun (acc, ann) id =>
    if ann then (acc, true)
    else match dag.kind? id with
    | some (NodeKind.constVal false) => (acc, true)
    | some (NodeKind.constVal true)  => (acc, ann)
    | some (NodeKind.andNode ch)     => (ch.foldl andInsert acc, ann)
    | _                              => (andInsert acc id, ann))
    (#[], false)

-- smart constructors

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

def mkXorCanon (dag : DAG) (ch : Array NodeId) : DAG × NodeId :=
  match ch.size with
  | 0 => dag.mkConst false
  | 1 => (dag, ch[0]!)
  | _ => dag.internNode (NodeKind.xorNode ch)

def mkAndCanon (dag : DAG) (ch : Array NodeId) (ann : Bool) : DAG × NodeId :=
  if ann then dag.mkConst false
  else match ch.size with
  | 0 => dag.mkConst true
  | 1 => (dag, ch[0]!)
  | _ => dag.internNode (NodeKind.andNode ch)

def mkXor (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  dag.mkXorCanon (dag.flattenXor ids)

def mkAnd (dag : DAG) (ids : Array NodeId) : DAG × NodeId :=
  let (ch, ann) := dag.flattenAnd ids
  dag.mkAndCanon ch ann

-- factoring

def factorFreqs (dag : DAG) (xorCh : Array NodeId) : HashMap NodeId Nat :=
  xorCh.foldl (fun freq id =>
    match dag.kind? id with
    | some (NodeKind.andNode fac) => fac.foldl (fun m f => m.insert f (m[f]?.getD 0 + 1)) freq
    | _ => freq)
    {}

def bestFactor (freq : HashMap NodeId Nat) : Option NodeId :=
  (freq.fold (fun best fac cnt =>
    if cnt < 2 then best
    else match best with
         | none          => some (fac, cnt)
         | some (bf, bc) =>
           if cnt > bc || (cnt == bc && fac < bf) then some (fac, cnt)
           else best)
    none).map (·.fst)

def stripFactor (dag : DAG) (id factor : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.andNode fac) =>
    let i := lowerBound fac factor
    if i < fac.size && fac[i]! == factor
    then dag.mkAndCanon (fac.eraseIdx! i) false
    else (dag, id)
  | _ => (dag, id)

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

partial def factorNode (dag : DAG) (id : NodeId) : DAG × NodeId :=
  match dag.kind? id with
  | some (NodeKind.xorNode xorCh) =>
    let (dag, xorCh') :=
      xorCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    let (dag, id') := dag.mkXor xorCh'
    match dag.kind? id' with
    | some (NodeKind.xorNode ch) =>
      match bestFactor (factorFreqs dag ch) with
      | none   => (dag, id')
      | some f =>
        let (dag, id'') := applyFactor dag ch f
        factorNode dag id''
    | _ => (dag, id')
  | some (NodeKind.andNode andCh) =>
    let (dag, andCh') :=
      andCh.foldl (fun (d, acc) cid =>
        let (d', cid') := factorNode d cid
        (d', acc.push cid'))
        (dag, #[])
    dag.mkAnd andCh'
  | _ => (dag, id)

def factor (dag : DAG) (ids : Array NodeId) : DAG × Array NodeId :=
  ids.foldl (fun (d, roots) id =>
              let (d', id') := d.factorNode id
              (d', roots.push id'))
            (dag, #[])

-- pretty

partial def ppNode (dag : DAG) (id : NodeId) : String :=
  match dag.kind? id with
  | none                                    => s!"[invalid:{id}]"
  | some (NodeKind.constVal true)           => "1"
  | some (NodeKind.constVal false)          => "0"
  | some (NodeKind.leaf (VarType.Secret s)) => s
  | some (NodeKind.leaf (VarType.Random r)) => r
  | some (NodeKind.leaf (VarType.Public p)) => s!"p({p})"
  | some (NodeKind.xorNode ch)              =>
    "(" ++ String.intercalate " + " (ch.toList.map (ppNode dag)) ++ ")"
  | some (NodeKind.andNode ch)              =>
    "(" ++ String.intercalate " * " (ch.toList.map (ppNode dag)) ++ ")"

end DAG

end verif
