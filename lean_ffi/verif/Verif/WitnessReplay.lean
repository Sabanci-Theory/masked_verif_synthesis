import Verif.«n-aryDAG»
import Verif.Rewrite
import Std.Data.HashMap

namespace verif

open Std (HashMap)

/-!
# Witness Replay — maskVerif-style probe-set extension

This module replaces the topological-greedy *closure* as the mechanism for
extending a certified probe set, following maskVerif (Barthe et al., CCS 2019,
`checker.ml`/`state.ml`) and the EUROCRYPT 2015 paper (Algorithms 3–4).

The idea: when the optimistic-sampling checker certifies a representative tuple
`y`, it leaves behind a **witness** `B` — the ordered sequence of optimistic
sampling substitutions `r ← e + r` it applied (maskVerif's `s_bij`, extracted by
`get_bij`).  That witness can then be *replayed* on any other observation `o`
(`replay_bij` + `is_top_expr`, i.e. Algorithm 3 `recheck`); the observations on
which the replay still reduces to a secret-free expression can be added to `y`
for free, yielding the extended safe set `ŷ` (Algorithm 4 `extend`).

This is the witness-replay counterpart of the closure: instead of a structural
dataflow deduction over the netlist, the *algebraic* rewrite history certifies
the extension.  The underlying rewrite engine (`Rewrite.lean`) is reused
unchanged — `checkWithWitness` is the substitution-based checker
(`rewriteComplete`) with a witness accumulator threaded through it.
-/

-- ============================================================
-- Witness
-- ============================================================

/-- A replayable optimistic-sampling derivation: an ordered list of steps
    `(r, e)`, each meaning "substitute `r ← e + r`".  This is maskVerif's
    `s_bij`/`bijection`, recorded as `(random, additive-context)` pairs because
    the existing engine replays a step via `substTupleByE _ _ r e`. -/
abbrev Witness := Array (NodeId × NodeId)

-- ============================================================
-- Check with witness capture  (≈ maskVerif `simplify_until` + `get_bij`)
-- ============================================================

/-- Witness-capturing clone of `rewriteComplete` (`Rewrite.lean`).

    Identical selection/substitution logic — `findSimpleRandom` then
    `findGeneralRandom`, each discharged by `substTupleByE` — so it certifies
    *exactly* what the kept engine certifies; it merely records each applied
    `r ← e + r` step into `witness`.  No factoring is performed (maskVerif does
    no multiplicative factoring; the optimistic-sampling rule needs only the
    additive structure).

    Termination mirrors `rewriteComplete`: each general step retires one random
    into `used` (never repeated for it); between general steps the simple rule
    strictly shrinks the tuple; `fuel` is a sound safety net (exhausting it
    returns `false`, only ever a false negative). -/
partial def rewriteWithWitness (g : GlobalDAG) (tuple : Array NodeId)
    (used : HashMap NodeId Unit) (witness : Witness) (fuel : Nat)
    : GlobalDAG × Bool × Witness :=
  if !tupleHasSecret g.dag tuple then (g, true, witness)
  else if fuel == 0 then (g, false, witness)
  else
    let s : DFSState := tuple.foldl (dfsRoot g.dag) {}
    let rootSet : HashMap NodeId Unit := tuple.foldl (fun m r => m.insert r ()) {}
    match findSimpleRandom g.dag s rootSet with
    | some (r, x1) =>
      let (g, e)      := contextOf g x1 r
      let (g, tuple') := substTupleByE g tuple r e
      rewriteWithWitness g tuple' used (witness.push (r, e)) (fuel - 1)
    | none =>
      match findGeneralRandom g.dag s rootSet used with
      | some (r, x1) =>
        let (g, e)      := contextOf g x1 r
        let (g, tuple') := substTupleByE g tuple r e
        rewriteWithWitness g tuple' (used.insert r ()) (witness.push (r, e)) (fuel - 1)
      | none => (g, false, witness)

/-- Entry point: certify `tuple` and, on success, return the replayable witness.
    Same fuel budget as `checkProbeComplete`. -/
def checkWithWitness (g : GlobalDAG) (tuple : Array NodeId)
    : GlobalDAG × Bool × Witness :=
  rewriteWithWitness g tuple {} #[] ((g.dag.randoms.size + 2) * 256)

-- ============================================================
-- Replay  (≈ maskVerif `replay_bij` + `is_top_expr`; Algorithm 3 `recheck`)
-- ============================================================

/-- Replay a witness on a tuple of observation roots: apply every recorded
    `r ← e + r` substitution in order (`substTupleByE` re-canonicalises via
    `mkXor`, so matched occurrences collapse to a bare `r` and others absorb
    `e`), then run the probing `Test` — is the result free of secrets?

    Soundness is the optimistic-sampling lemma: each step preserves the joint
    distribution, so a secret-free result certifies the tuple's independence. -/
def replayWitness (g : GlobalDAG) (witness : Witness) (roots : Array NodeId)
    : GlobalDAG × Bool :=
  let (g, roots') := witness.foldl (fun (acc : GlobalDAG × Array NodeId) re =>
    let (g, roots) := acc
    substTupleByE g roots re.1 re.2) (g, roots)
  (g, !tupleHasSecret g.dag roots')

-- ============================================================
-- Extend  (≈ maskVerif `find_bij` partition; Algorithm 4 `extend`)
-- ============================================================

/-- Extend the certified representative `chosen` to a larger safe set by
    replaying `witness` on each candidate observation and keeping those that
    still reduce to a secret-free expression.

    Per-candidate replay is the literal Algorithm 4 reading; it is sound for the
    *joint* set by the recheck-union lemma (if `recheck(e,h)` and
    `recheck(e',h)` then `recheck(e ∪ e',h)`), given `chosen` itself was
    certified by `witness`.  Every wire in `chosen` replays to a secret-free
    expression, so the returned set always contains `chosen`. -/
def extendByReplay (g : GlobalDAG) (witness : Witness)
    (candidates : Array (String × NodeId)) : GlobalDAG × Array String :=
  candidates.foldl (fun (acc : GlobalDAG × Array String) c =>
    let (g, safe) := acc
    let (g, ok) := replayWitness g witness #[c.2]
    if ok then (g, safe.push c.1) else (g, safe)) (g, #[])

end verif
