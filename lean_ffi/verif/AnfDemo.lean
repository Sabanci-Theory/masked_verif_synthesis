import Verif

/-!
Demonstration that the coupling extension's exact ANF test blinds a wire that
witness-replay's XOR-canonicalisation test cannot.

  w = (s+r)·(s+r+1) + r·r₂

As a polynomial this is `r·r₂` (secret-free: `(s+r)(s+r+1) = 0` in 𝔽₂).  But the
DAG keeps the product unexpanded, so a `Secret` leaf `s` is still syntactically
reachable — `tupleHasSecret w = true`.  Witness replay decides secret-freeness by
exactly that syntactic test, so it rejects `w`.  Our ANF fallback expands the
product, sees the cancellation, and accepts `w`.
-/

namespace verif
open Std (HashMap)

def demoG : GlobalDAG :=
  ({} : GlobalDAG)
  |>.addShare "a"  #[.leaf (.Secret "s"), .leaf (.Random "r")]                 -- s + r
  |>.addShare "b"  #[.leaf (.Secret "s"), .leaf (.Random "r"), .const true]    -- s + r + 1
  |>.addWireAnd "ab" #[.wire "a", .wire "b"]                                   -- (s+r)(s+r+1) = 0
  |>.addWireAnd "cd" #[.leaf (.Random "r"), .leaf (.Random "r2")]             -- r·r₂
  |>.addWireXor "w"  #[.wire "ab", .wire "cd"]                                 -- w = r·r₂
  |>.addShare "o"  #[.leaf (.Secret "s2"), .leaf (.Random "r3")]              -- chosen probe

#eval do
  let g := demoG
  let wNode := (g.wires["w"]?).get!
  let oNode := (g.wires["o"]?).get!
  IO.println "=== ANF demo:  w = (s+r)(s+r+1) + r·r2   ( = r·r2, secret-free ) ==="
  IO.println s!"  witness test  tupleHasSecret(w) = {tupleHasSecret g.dag #[wNode]}   (true ⇒ witness REJECTS w)"
  IO.println s!"  exact ANF     anfSecretFree(w)  = {anfSecretFree g.dag wNode}   (true ⇒ coupling ACCEPTS w)"
  let (g, secO, coupling) := checkProbeCompleteT g #[oNode]
  IO.println s!"  chosen o = s2+r3  certified={secO}  coupling.size={coupling.size} (touches r3 only)"
  let (_, safe, anfCount) := couplingExtend g coupling #["o"] #[("w", wNode)]
  IO.println s!"  couplingExtend → safe={safe}  anfFallbacks={anfCount}"

end verif
