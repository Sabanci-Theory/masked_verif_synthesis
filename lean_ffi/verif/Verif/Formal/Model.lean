namespace verif.Formal

/-!
# Formal Model — Boolean Expressions over Secret/Random/Public Leaves

The deep embedding the soundness proof is stated against.  Leaves are indexed
by `Nat`: secrets and publics are interpreted by arbitrary assignments
`σ π : Nat → Bool` (the security statement quantifies over them), randoms by a
finite tape `ρ : List Bool` (index `i` reads `ρ.getD i false`), over which the
probability layer (`Tape.lean`) counts.

Everything here is *total* — structural recursion only.  The untrusted tool
(hash-consed DAG, rewrite engine, factoring, PIT, budgeted ANF) never appears:
its output is re-validated against this model by the verified checker.
-/

/-- Deep-embedded 𝔽₂ expression.  Binary gates suffice for the model; the
    tool's n-ary canonicalised DAG is an untrusted optimisation. -/
inductive BExpr where
  | const  : Bool  → BExpr
  | secret : Nat   → BExpr
  | rand   : Nat   → BExpr
  | pub    : Nat   → BExpr
  | bxor   : BExpr → BExpr → BExpr
  | band   : BExpr → BExpr → BExpr
  deriving Repr, DecidableEq, Inhabited

namespace BExpr

/-- Semantics: secrets/publics from `σ`/`π`, randoms from the tape `ρ`
    (out-of-range indices read `false`; the well-formed checker only emits
    indices below the tape length). -/
def eval (σ π : Nat → Bool) (ρ : List Bool) : BExpr → Bool
  | const b  => b
  | secret i => σ i
  | rand i   => ρ.getD i false
  | pub i    => π i
  | bxor a b => xor (eval σ π ρ a) (eval σ π ρ b)
  | band a b => eval σ π ρ a && eval σ π ρ b

/-- Does `w` mention the random of index `i`? -/
def mentionsRand : BExpr → Nat → Bool
  | rand j,   i => j == i
  | bxor a b, i => mentionsRand a i || mentionsRand b i
  | band a b, i => mentionsRand a i || mentionsRand b i
  | _,        _ => false

/-- Does `w` syntactically contain a secret leaf?  (Sound but incomplete for
    semantic secret-dependence; the complete test is polynomial normalisation,
    `Poly.lean`.) -/
def hasSecret : BExpr → Bool
  | secret _ => true
  | bxor a b => hasSecret a || hasSecret b
  | band a b => hasSecret a || hasSecret b
  | _        => false

/-- Substitute every occurrence of the random leaf `rand r` by `t`. -/
def substR (r : Nat) (t : BExpr) : BExpr → BExpr
  | rand j   => if j == r then t else rand j
  | bxor a b => bxor (substR r t a) (substR r t b)
  | band a b => band (substR r t a) (substR r t b)
  | w        => w

/-- `w` is *semantically* secret-free: its value never depends on the secret
    assignment.  This is the acceptance condition of the coupling extension;
    the syntactic `hasSecret = false` and the polynomial normal form both
    imply it. -/
def SemSecretFree (w : BExpr) : Prop :=
  ∀ (σ₁ σ₂ π : Nat → Bool) (ρ : List Bool), eval σ₁ π ρ w = eval σ₂ π ρ w

-- ============================================================
-- Congruence lemmas
-- ============================================================

/-- `eval` only reads tape indices that `w` mentions. -/
theorem eval_congr_rand {σ π : Nat → Bool} {ρ₁ ρ₂ : List Bool} :
    ∀ (w : BExpr),
      (∀ i, mentionsRand w i = true → ρ₁.getD i false = ρ₂.getD i false) →
      eval σ π ρ₁ w = eval σ π ρ₂ w
  | const _,  _ => rfl
  | secret _, _ => rfl
  | pub _,    _ => rfl
  | rand i,   h => h i (by simp [mentionsRand])
  | bxor a b, h => by
      simp only [eval]
      rw [eval_congr_rand a (fun i hi => h i (by simp [mentionsRand, hi])),
          eval_congr_rand b (fun i hi => h i (by simp [mentionsRand, hi]))]
  | band a b, h => by
      simp only [eval]
      rw [eval_congr_rand a (fun i hi => h i (by simp [mentionsRand, hi])),
          eval_congr_rand b (fun i hi => h i (by simp [mentionsRand, hi]))]

/-- Syntactic secret-freeness implies semantic secret-freeness. -/
theorem semSecretFree_of_not_hasSecret :
    ∀ (w : BExpr), hasSecret w = false → SemSecretFree w
  | const _,  _, _,  _,  _, _ => rfl
  | pub _,    _, _,  _,  _, _ => rfl
  | rand _,   _, _,  _,  _, _ => rfl
  | secret _, h, _,  _,  _, _ => by simp [hasSecret] at h
  | bxor a b, h, σ₁, σ₂, π, ρ => by
      have ha : hasSecret a = false := by
        cases hEq : hasSecret a <;> simp [hasSecret, hEq] at h ⊢
      have hb : hasSecret b = false := by
        cases hEq : hasSecret b <;> simp [hasSecret, hEq] at h ⊢
      simp only [eval]
      rw [semSecretFree_of_not_hasSecret a ha σ₁ σ₂ π ρ,
          semSecretFree_of_not_hasSecret b hb σ₁ σ₂ π ρ]
  | band a b, h, σ₁, σ₂, π, ρ => by
      have ha : hasSecret a = false := by
        cases hEq : hasSecret a <;> simp [hasSecret, hEq] at h ⊢
      have hb : hasSecret b = false := by
        cases hEq : hasSecret b <;> simp [hasSecret, hEq] at h ⊢
      simp only [eval]
      rw [semSecretFree_of_not_hasSecret a ha σ₁ σ₂ π ρ,
          semSecretFree_of_not_hasSecret b hb σ₁ σ₂ π ρ]

-- ============================================================
-- The substitution lemma
-- ============================================================

/-- **Substitution lemma**: substituting `rand r ← t` and evaluating equals
    evaluating with the tape updated at `r` to `t`'s value.  Requires `r` to
    lie inside the tape (`List.set` is a no-op out of range, while `substR`
    is not). -/
theorem eval_substR (σ π : Nat → Bool) (ρ : List Bool) (r : Nat) (t : BExpr)
    (hr : r < ρ.length) :
    ∀ w : BExpr, eval σ π ρ (substR r t w)
      = eval σ π (ρ.set r (eval σ π ρ t)) w
  | .const _  => rfl
  | .secret _ => rfl
  | .pub _    => rfl
  | .rand j   => by
      by_cases hj : j = r
      · subst hj
        simp [substR, eval, List.getD_eq_getElem?_getD, List.getElem?_set_self hr]
      · simp [substR, hj, eval, List.getD_eq_getElem?_getD,
              List.getElem?_set_ne (fun h => hj h.symm)]
  | .bxor a b => by
      simp only [substR, eval]
      rw [eval_substR σ π ρ r t hr a, eval_substR σ π ρ r t hr b]
  | .band a b => by
      simp only [substR, eval]
      rw [eval_substR σ π ρ r t hr a, eval_substR σ π ρ r t hr b]

end BExpr

end verif.Formal
