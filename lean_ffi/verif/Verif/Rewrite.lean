import Verif.«n-aryDAG»
import Std.Data.HashMap

namespace verif

open Std (HashMap)

namespace Rewrite

abbrev ParentMap := HashMap NodeId (Array NodeId)

/-- DFS: visits `id`, records the given `id` as parent of each of its children. -/
partial def computeParentsAux
    (dag     : DAG)
    (id      : NodeId)
    (parents : ParentMap)
    (visited : HashMap NodeId Unit)
    : ParentMap × HashMap NodeId Unit :=
  if visited.contains id then (parents, visited)
  else
    let visited := visited.insert id ()
    match dag.kind? id with
    | some (NodeKind.xorNode ch)
    | some (NodeKind.andNode ch) =>
      ch.foldl (fun (p, v) cid =>
        -- Record `id` as a parent of `cid`, then recurse into `cid`.
        let p' := p.insert cid (((p.get? cid).getD #[]).push id)
        computeParentsAux dag cid p' v)
        (parents, visited)
    | _ => (parents, visited)

/-- Computes the parent map for the subgraph reachable from `roots`. -/
def computeParents (dag : DAG) (roots : Array NodeId) : ParentMap :=
  (roots.foldl (fun (p, v) root => computeParentsAux dag root p v)
    ({}, {})).1

/-- Tests if `id` is a random leaf that appears as a sole child of an xorNode -/
def isStandaloneXorRandom (dag : DAG) (parents : ParentMap) (id : NodeId) : Bool :=
  match dag.kind? id with
  | some (NodeKind.leaf (VarType.Random _)) =>
    match parents.get? id with
    | some ps =>
      ps.size == 1 &&
      match dag.kind? ps[0]! with
      | some (.xorNode _) => true
      | _                 => false
    | none => false   -- random not reachable from any root
  | _ => false

/-- Returns all random leaves that are standalone XOR'ed within the expressions
    rooted at `roots`. -/
def findStandaloneXorRandoms (dag : DAG) (roots : Array NodeId) : Array NodeId :=
  let parents := computeParents dag roots
  dag.randoms.filter (isStandaloneXorRandom dag parents)

end Rewrite

def example2 : String :=
  let dag : DAG := {}
  let (dag, e)  := dag.mkLeaf (VarType.Public "e")
  let (dag, a)  := dag.mkLeaf (VarType.Secret "a")
  let (dag, b)  := dag.mkLeaf (VarType.Secret "b")
  let (dag, r0) := dag.mkLeaf (VarType.Random "r0")
  let (dag, ea)   := dag.mkAnd #[e, a]
  let (dag, eb)   := dag.mkAnd #[e, b]
  let (dag, root) := dag.mkXor #[ea, eb, r0]
  let (dag', fac) := dag.factor root
  let standalone  := Rewrite.findStandaloneXorRandoms dag' #[fac]
  s!"Before : {dag.ppNode root}\n" ++
  s!"After  : {dag'.ppNode fac}\n" ++
  s!"Rewritable randoms : {standalone.toList.map (dag'.ppNode)}"

#eval IO.println example2


def example3 : String :=
  let dag : DAG := {}
  let (dag, e)  := dag.mkLeaf (VarType.Public "e")
  let (dag, a)  := dag.mkLeaf (VarType.Secret "a")
  let (dag, b)  := dag.mkLeaf (VarType.Secret "b")
  let (dag, r0) := dag.mkLeaf (VarType.Random "r0")
  let (dag, ea)    := dag.mkAnd #[e, a]
  let (dag, eb)    := dag.mkAnd #[e, b]
  let (dag, wire1) := dag.mkXor #[ea, r0]
  let (dag, wire2) := dag.mkXor #[eb, r0]
  let roots        := #[wire1, wire2]
  let standalone   := Rewrite.findStandaloneXorRandoms dag roots
  s!"wire1 : {dag.ppNode wire1}\n" ++
  s!"wire2 : {dag.ppNode wire2}\n" ++
  s!"Rewritable randoms : {standalone.toList.map (dag.ppNode)}"

#eval IO.println example3

end verif
