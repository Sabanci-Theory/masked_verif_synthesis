import Verif.Formal.Coupling
import Verif.Formal.Poly

namespace verif.Formal

open BExpr

/-!
# The Verified Certificate Checker (single probe region)

Executable acceptance for one certified region, with its soundness theorem.
The untrusted engine proposes `(ws, T)` — the chosen probe tuple together with
the extension candidates it claims to blind, and the derivation coupling —
and `checkCoupledTuple` re-validates everything in the model:

1. every step of `T` is a legal relabel (`validCoupling`);
2. every image under `T` is secret-free, decided *exactly* by multilinear
   normalisation (`polySecretFree ∘ toPoly`), which absorbs the engine's
   syntactic acceptance, its budgeted-ANF acceptance, and factoring.

A `true` answer yields joint independence of `ws` (`checkCoupledTuple_sound`)
and hence of every probe drawn from `ws` in any order and multiplicity
(`checkCoupledTuple_covers`) — the formal soundness of the coupling-driven
probe-set extension.  A wrong or garbled certificate can only produce `false`
(a completeness loss), never an unsound acceptance.
-/

/-- Boolean (executable) form of `ValidCoupling`. -/
def validCoupling (n : Nat) (T : Coupling) : Bool :=
  T.all (fun p => decide (p.1 < n) && !mentionsRand p.2 p.1)

theorem validCoupling_sound {n : Nat} {T : Coupling}
    (h : validCoupling n T = true) : ValidCoupling n T := by
  intro p hp
  have hp' := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp'
  exact hp'

/-- Verified acceptance of one certified region.  `n` is the tape length
    (number of circuit randoms), `ws` the region tuple (chosen probe ++
    accepted extension candidates), `T` the engine's coupling. -/
def checkCoupledTuple (n : Nat) (ws : List BExpr) (T : Coupling) : Bool :=
  validCoupling n T
    && (applyCoupling T ws).all (fun w => polySecretFree (toPoly w))

/-- **Soundness of the checker**: acceptance implies the joint distribution
    of `ws` is independent of the secrets. -/
theorem checkCoupledTuple_sound {n : Nat} {ws : List BExpr} {T : Coupling}
    (h : checkCoupledTuple n ws T = true) : IndepOfSecrets n ws := by
  unfold checkCoupledTuple at h
  rw [Bool.and_eq_true] at h
  exact coupling_blinds (validCoupling_sound h.1)
    (fun w hw => semSecretFree_of_polySecretFree w
      (List.all_eq_true.mp h.2 w hw))

/-- **Soundness of the extension**: acceptance covers every probe drawn from
    the certified region — any subset, any order, any multiplicity. -/
theorem checkCoupledTuple_covers {n : Nat} {ws : List BExpr} {T : Coupling}
    (h : checkCoupledTuple n ws T = true)
    {probe : List BExpr} (hmem : ∀ w ∈ probe, w ∈ ws) :
    IndepOfSecrets n probe :=
  mem_indep (checkCoupledTuple_sound h) hmem

-- ============================================================
-- The d-probing security statement
-- ============================================================

/-- `d`-probing security of a wire tuple over a length-`n` tape: every probe
    of at most `d` wires is jointly independent of the secrets.  Probes are
    quantified as arbitrary member-lists (order and multiplicity are
    irrelevant by `mem_indep`, so this is equivalent to quantifying over
    subsets). -/
def ProbingSecure (n : Nat) (wires : List BExpr) (d : Nat) : Prop :=
  ∀ probe : List BExpr, (∀ w ∈ probe, w ∈ wires) → probe.length ≤ d →
    IndepOfSecrets n probe

/-- A single certificate whose region contains *all* wires certifies any
    probing order at once (the tool's `union` discharge). -/
theorem probingSecure_of_union {n : Nat} {wires : List BExpr} {T : Coupling}
    (h : checkCoupledTuple n wires T = true) (d : Nat) :
    ProbingSecure n wires d :=
  fun _ hmem _ => checkCoupledTuple_covers h hmem

-- ============================================================
-- End-to-end sanity instances (decided by kernel reduction)
-- ============================================================

/-- The masked wire `s ⊕ r`: the coupling step `r ← s ⊕ r` blinds it.
    Its image is `s ⊕ (s ⊕ r)`, accepted only because normalisation cancels
    `s` — the syntactic check would fail here. -/
example :
    checkCoupledTuple 1 [bxor (secret 0) (rand 0)] [(0, secret 0)] = true := by
  decide

/-- ... and therefore `[s ⊕ r]` is distributed independently of `s`. -/
example : IndepOfSecrets 1 [bxor (secret 0) (rand 0)] :=
  checkCoupledTuple_sound (n := 1) (T := [(0, secret 0)]) (by decide)

/-- Product cancellation (the `AnfDemo` scenario): the image of
    `(s⊕r)·(s⊕r)` under `r ← s ⊕ r` still *syntactically* contains `s`
    (`(s⊕(s⊕r))·(s⊕(s⊕r))`), so the tool's phase-2 check would reject it —
    but normalisation cancels to the bare `r`, and the verified test
    accepts.  This is the coupling ⊋ witness-replay separation, verified. -/
example :
    checkCoupledTuple 1
      [band (bxor (secret 0) (rand 0)) (bxor (secret 0) (rand 0))]
      [(0, secret 0)] = true := by
  decide

/-- An *invalid* certificate (context mentions its own random) is rejected
    regardless of what it claims to blind. -/
example :
    validCoupling 1 [(0, bxor (secret 0) (rand 0))] = false := by
  decide

/-- A certificate that fails to blind (probing `s` directly) is rejected. -/
example :
    checkCoupledTuple 1 [secret 0] [(0, secret 0)] = false := by
  decide

end verif.Formal
