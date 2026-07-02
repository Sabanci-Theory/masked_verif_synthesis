import Verif

/-!
Regression test for the probed-root relabel bug (fixed 2026-07-02).

A probed wire that *aliases* a bare random (`w1 = r`, a 1-input XOR, which
`mkXorCanon` collapses to the leaf node of `r`) plus two more occurrences of
`r`.  The tuple {w1, w2, w3} = (r, s+r, r+r3) leaks `s` (w1 ⊕ w2 = s), so the
correct verdict is INSECURE at every order ≥ 2.

The bug: `decrementParent`'s cascade re-insertion had no root check, so after
`r3` was eliminated, `r` (tpc 2→1, xpc 2→1) was pushed onto `todo` even though
`r` is a probe ROOT, and `applyRewrite` relabeled the observed `r` via its
parent `w2 = s+r`, hiding `s` → false SECURE in the reference-counted tier.
The fix guards the re-insertion with `ps.rootSet`.
-/

namespace verif

def bugG : GlobalDAG :=
  ({} : GlobalDAG)
  |>.addWireXor "w1" #[.leaf (.Random "r")]                        -- w1 = r  (alias)
  |>.addWireXor "w2" #[.leaf (.Secret "s"), .leaf (.Random "r")]   -- w2 = s + r
  |>.addWireXor "w3" #[.leaf (.Random "r"), .leaf (.Random "r3")]  -- w3 = r + r3

#eval do
  let g := bugG
  let ids := #["w1", "w2", "w3"].filterMap (g.wires[·]?)
  IO.println s!"tuple = (r, s+r, r+r3); truth: INSECURE (w1+w2 = s)"
  let (_, sec1) := checkProbeRoots g ids
  IO.println s!"checkProbeRoots (tiered engine)   secure = {sec1}   (expect false)"
  let (_, sec3, _) := checkProbeCompleteT g ids
  IO.println s!"checkProbeCompleteT (general loop) secure = {sec3}   (expect false)"
  let (_, _, res2, _) := checkDProbing g 2 true
  IO.println s!"checkDProbing order 2 (extend) : {ppResult res2 2}"
  let (_, _, res2n, _) := checkDProbing g 2 false
  IO.println s!"checkDProbing order 2 (naive)  : {ppResult res2n 2}"
  let (_, _, res3, _) := checkDProbing g 3 true
  IO.println s!"checkDProbing order 3 (extend) : {ppResult res3 3}"
  if sec1 || sec3 || res2.isSecure || res2n.isSecure || res3.isSecure then
    IO.println "*** REGRESSION: false SECURE — the probed-root relabel bug is back ***"
  else
    IO.println "OK: all paths report INSECURE."

end verif
