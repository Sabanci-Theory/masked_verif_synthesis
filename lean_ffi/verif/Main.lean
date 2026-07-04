import Verif

namespace verif

/-!
# Examples and the `=== Results ===` ablation

The example gadgets and the coupling-vs-naive ablation runner, moved out of
`ProbeClosure.lean` so the library builds without running the benchmark.
Run with `lake exe verif`.
-/

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


/-! ## Example 2 — XOR-linear relation between wires

    w1 = a + r1,  w2 = b + r2,  w3 = w1 + w2

    Probing w3 alone is secure (uniform via r1, r2).  At order 2 every pair is
    secure; e.g. for a chosen probe containing {w1, w3}, the coupling `T` that
    certifies it also blinds w2 = w1 + w3 (w2∘T is secret-free), so the coupling
    extension adds w2 to the certified-safe set. -/
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

    Two wires whose expressions canonicalise to the same DAG node (both `a + r`).
    Probing either one, the coupling that blinds it blinds the other identically
    (same node ⇒ same `w∘T`), so the extension covers both. -/
def circuitC : GlobalDAG := ({} : GlobalDAG)
  |>.addWireXor "w1" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]
  |>.addWireXor "w2" #[WireInput.leaf (VarType.Secret "a"), WireInput.leaf (VarType.Random "r")]


/-! ## Example 5 — containment via shared intermediate

    w1a = a + r,  w1 = w1a + b   (b is a Public leaf)
    w2  = a + r

    Decomposing w1 to 2-ary exposes the intermediate `w1a = a + r`, whose DAG
    node is hash-cons-identical to `w2`.  At order 1, probing w1 certifies it via
    a coupling `T` (blinding r); the same `T` blinds w1a and w2 as well (their
    `w∘T` are secret-free — indeed w1a and w2 are the same node), so the coupling
    extension adds both. -/
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

/-! ## Example 8 — n-share DOM-independent AND, parameterized

    Generalizes the former hand-written 7-share instance to any `shares ≥ 2`:
      input shares   a_i = r_a_i (i < n-1),  a_{n-1} = a + Σ_i r_a_i  (same for b)
      diagonals      u_i  = a_i·b_i
      cross products p_ij = a_i·b_j                    (i ≠ j)
      masked terms   c_ij = p_ij + r_ij,  r_ij = r_ji  (one fresh random per unordered pair)
      outputs        s_i  = u_i + Σ_{j≠i} c_ij         (2-ary chain; the mask is
                     grouped with its cross term inside c_ij, which is the
                     security-relevant association)
    Wire naming and emission order (shares, diagonals, all cross products, all
    masked terms, outputs) match the old `sevenDomAND`, so `domAND 7` is the
    former example verbatim.  An n-share DOM-AND is expected to be
    (n-1)-probing secure.  NOTE: names are only unambiguous for `shares ≤ 10`
    (two digits concatenate in `p{i}{j}`). -/
def domAND (shares : Nat) : GlobalDAG := Id.run do
  let mut g : GlobalDAG := {}
  -- input shares: first n-1 are bare randoms, the last carries the secret
  for (pre, sec) in #[("a", "a"), ("b", "b")] do
    let mut last : Array WireInput := #[.leaf (.Secret sec)]
    for i in [0:shares-1] do
      g := g.addShare s!"{pre}{i}" #[.leaf (.Random s!"r{pre}{i}")]
      last := last.push (.leaf (.Random s!"r{pre}{i}"))
    g := g.addShare s!"{pre}{shares-1}" last
  -- diagonal products
  for i in [0:shares] do
    g := g.addWireAnd s!"u{i}" #[.wire s!"a{i}", .wire s!"b{i}"]
  -- cross products
  for i in [0:shares] do
    for j in [i+1:shares] do
      g := g.addWireAnd s!"p{i}{j}" #[.wire s!"a{i}", .wire s!"b{j}"]
      g := g.addWireAnd s!"p{j}{i}" #[.wire s!"a{j}", .wire s!"b{i}"]
  -- masked cross terms
  for i in [0:shares] do
    for j in [i+1:shares] do
      let r := WireInput.leaf (.Random s!"r{i}{j}")
      g := g.addWireXor s!"c{i}{j}" #[.wire s!"p{i}{j}", r]
      g := g.addWireXor s!"c{j}{i}" #[.wire s!"p{j}{i}", r]
  -- outputs
  for i in [0:shares] do
    let mut terms : Array WireInput := #[.wire s!"u{i}"]
    for j in [0:shares] do
      if j != i then
        terms := terms.push (.wire s!"c{i}{j}")
    g := addWireXorChain g s!"s{i}" terms
  return g

/-- The former hand-written Example 8, now an instance of `domAND`. -/
def sevenDomAND : GlobalDAG := domAND 7

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

/-! ## Comparison: coupling extension vs. the naive (no-extension) baseline

    Runs each instance twice — once with the coupling extension growing every
    certified probe set (`extend := true`), once with no extension
    (`extend := false`), where each representative covers only its own subsets and
    the space-split degrades toward exhaustive enumeration.  Both use the same
    sound rewrite checker, so the verdicts must agree; only the discharge count and
    wall-clock differ. -/
def ppAblation (name : String) (g : GlobalDAG) (order : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (_, _, resC, sC) := checkDProbing g order true
  let t1 ← IO.monoMsNow
  let (_, _, resN, sN) := checkDProbing g order false
  let t2 ← IO.monoMsNow
  let v := fun (r : CheckResult) => if r.isSecure then "secure" else "INSECURE"
  IO.println s!"{name} @ order {order}:  coupling {v resC}  |  naive {v resN}  (agree={resC.isSecure == resN.isSecure})"
  IO.println s!"    coupling     : {t1 - t0} ms\n{sC.pp}\n"
  IO.println s!"    no extension : {t2 - t1} ms\n{sN.pp}\n"



def runAblation : IO Unit := do
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
  -- Cross-checks of the parameterized constructor against the hand-written
  -- instances above (expected: INSECURE at n=2/order 2, secure at n=3/order 2).
  ppAblation "DOM-AND (generic, 2 shares)" (domAND 2) 2
  ppAblation "DOM-AND (generic, 3 shares)" (domAND 3) 2
  -- ppAblation "7-share DOM-AND" sevenDomAND 5
  ppAblation "Example x + yz" circuitE 2
  ppAblation "Example x + yz" circuitE 3

/-
  stored output (pre-coupling closure ablation, kept for reference):
  7-share DOM-AND @ order 5:  verdict secure (agree=true)
      with closure   : 1072583 ms  | discharges 14256  certs 7113  free/main 0.532265
      without closure: 842942 ms  | discharges 9298  certs 4633
-/

end verif

def main : IO Unit :=
  verif.runAblation

#eval main
