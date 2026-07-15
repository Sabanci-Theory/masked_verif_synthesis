import Verif.Formal.Model

namespace verif.Formal

open BExpr

/-!
# Verified Multilinear Normalisation (ANF) — Exact Secret-Freeness Test

The verified counterpart of the tool's budgeted ANF (`Verif/Coupling.lean`)
and, at the same time, of its *factoring* acceptances: the checker decides
secret-freeness of a coupling image `w∘T` by normalising to a multilinear
𝔽₂ polynomial and inspecting the surviving monomials.  Only the **sound**
direction is proved (test passes ⇒ semantically secret-free), which is all
soundness of the tool needs; canonicity/completeness of the normal form is
deliberately not formalised.

Design note: monomials are kept sorted-and-deduplicated and equal monomials
are cancelled by `togglePoly`, but *no invariant about this is ever needed* —
every operation carries its own semantics lemma (`x·x = x`, `m ⊕ m = 0` hold
pointwise in `Bool`), so ill-sorted input would only cost cancellation
power (completeness), never soundness.
-/

/-- A polynomial variable: one leaf of the model. -/
inductive PVar where
  | secret : Nat → PVar
  | rand   : Nat → PVar
  | pub    : Nat → PVar
  deriving Repr, DecidableEq, Inhabited

namespace PVar

def isSecret : PVar → Bool
  | secret _ => true
  | _        => false

/-- Sort key (order irrelevant to soundness; injectivity irrelevant too —
    dedup compares variables directly). -/
def key : PVar → Nat
  | secret i => 3 * i
  | rand i   => 3 * i + 1
  | pub i    => 3 * i + 2

def eval (σ π : Nat → Bool) (ρ : List Bool) : PVar → Bool
  | secret i => σ i
  | rand i   => ρ.getD i false
  | pub i    => π i

end PVar

/-- A monomial: a product of variables (kept sorted+distinct). -/
abbrev Mono := List PVar
/-- A polynomial: an XOR of monomials (kept cancelled). -/
abbrev Poly := List Mono

def evalMono (σ π : Nat → Bool) (ρ : List Bool) (m : Mono) : Bool :=
  m.foldr (fun v acc => PVar.eval σ π ρ v && acc) true

def evalPoly (σ π : Nat → Bool) (ρ : List Bool) (p : Poly) : Bool :=
  p.foldr (fun m acc => xor (evalMono σ π ρ m) acc) false

-- Bool helpers (three-atom identities, by case exhaustion)
private theorem and_self_left (a b : Bool) : (a && (a && b)) = (a && b) := by
  cases a <;> cases b <;> rfl
private theorem and_left_comm (a b c : Bool) : (a && (b && c)) = (b && (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl
private theorem xor_xor_self (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl
private theorem xor_left_comm (a b c : Bool) : xor a (xor b c) = xor b (xor a c) := by
  cases a <;> cases b <;> cases c <;> rfl
private theorem and_xor_left (a b c : Bool) : (a && xor b c) = xor (a && b) (a && c) := by
  cases a <;> cases b <;> cases c <;> rfl
private theorem xor_and_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- ============================================================
-- Operations, each with its semantics lemma
-- ============================================================

/-- Sorted-dedup insert of a variable into a monomial (`x·x = x`). -/
def insertVar (v : PVar) : Mono → Mono
  | [] => [v]
  | w :: m =>
    if v = w then w :: m
    else if v.key < w.key then v :: w :: m
    else w :: insertVar v m

theorem evalMono_insertVar (σ π : Nat → Bool) (ρ : List Bool) (v : PVar) :
    ∀ m : Mono, evalMono σ π ρ (insertVar v m)
      = (PVar.eval σ π ρ v && evalMono σ π ρ m)
  | [] => rfl
  | w :: m => by
    by_cases hvw : v = w
    · subst hvw
      simp only [insertVar, evalMono, List.foldr_cons]
      exact (and_self_left _ _).symm
    · by_cases hk : v.key < w.key
      · simp only [insertVar, if_neg hvw, if_pos hk]
        rfl
      · simp only [insertVar, if_neg hvw, if_neg hk, evalMono, List.foldr_cons]
        show (PVar.eval σ π ρ w && evalMono σ π ρ (insertVar v m)) = _
        rw [evalMono_insertVar σ π ρ v m]
        exact and_left_comm _ _ _

/-- Monomial product (union of variable sets). -/
def monoMul (a b : Mono) : Mono :=
  a.foldr insertVar b

theorem evalMono_monoMul (σ π : Nat → Bool) (ρ : List Bool) :
    ∀ a b : Mono, evalMono σ π ρ (monoMul a b)
      = (evalMono σ π ρ a && evalMono σ π ρ b)
  | [], b => by simp [monoMul, evalMono]
  | v :: a, b => by
    show evalMono σ π ρ (insertVar v (monoMul a b)) = _
    rw [evalMono_insertVar, evalMono_monoMul σ π ρ a b]
    show _ = ((PVar.eval σ π ρ v && evalMono σ π ρ a) && evalMono σ π ρ b)
    rw [Bool.and_assoc]

/-- Toggle a monomial into a polynomial (`m ⊕ m = 0`). -/
def togglePoly (m : Mono) : Poly → Poly
  | [] => [m]
  | m' :: p => if m = m' then p else m' :: togglePoly m p

theorem evalPoly_togglePoly (σ π : Nat → Bool) (ρ : List Bool) (m : Mono) :
    ∀ p : Poly, evalPoly σ π ρ (togglePoly m p)
      = xor (evalMono σ π ρ m) (evalPoly σ π ρ p)
  | [] => by simp [togglePoly, evalPoly]
  | m' :: p => by
    by_cases hmm : m = m'
    · subst hmm
      simp only [togglePoly]
      exact (xor_xor_self _ _).symm
    · simp only [togglePoly, if_neg hmm, evalPoly, List.foldr_cons]
      show xor (evalMono σ π ρ m') (evalPoly σ π ρ (togglePoly m p)) = _
      rw [evalPoly_togglePoly σ π ρ m p]
      exact xor_left_comm _ _ _

/-- Polynomial sum (symmetric difference of monomial multisets). -/
def polyXor (p q : Poly) : Poly :=
  q.foldr togglePoly p

theorem evalPoly_polyXor (σ π : Nat → Bool) (ρ : List Bool) :
    ∀ q p : Poly, evalPoly σ π ρ (polyXor p q)
      = xor (evalPoly σ π ρ p) (evalPoly σ π ρ q)
  | [], p => by simp [polyXor, evalPoly]
  | m :: q, p => by
    show evalPoly σ π ρ (togglePoly m (polyXor p q)) = _
    rw [evalPoly_togglePoly, evalPoly_polyXor σ π ρ q p]
    show _ = xor (evalPoly σ π ρ p) (xor (evalMono σ π ρ m) (evalPoly σ π ρ q))
    rw [xor_left_comm]

theorem evalPoly_map_monoMul (σ π : Nat → Bool) (ρ : List Bool) (m : Mono) :
    ∀ q : Poly, evalPoly σ π ρ (q.map (monoMul m))
      = (evalMono σ π ρ m && evalPoly σ π ρ q)
  | [] => by simp [evalPoly]
  | m' :: q => by
    simp only [List.map_cons, evalPoly, List.foldr_cons]
    show xor (evalMono σ π ρ (monoMul m m')) (evalPoly σ π ρ (q.map (monoMul m))) = _
    rw [evalMono_monoMul, evalPoly_map_monoMul σ π ρ m q]
    exact (and_xor_left _ _ _).symm

/-- Polynomial product (distribute, cancelling as we go). -/
def polyMul (p q : Poly) : Poly :=
  p.foldr (fun m acc => polyXor acc (q.map (monoMul m))) []

theorem evalPoly_polyMul (σ π : Nat → Bool) (ρ : List Bool) :
    ∀ p q : Poly, evalPoly σ π ρ (polyMul p q)
      = (evalPoly σ π ρ p && evalPoly σ π ρ q)
  | [], q => by simp [polyMul, evalPoly]
  | m :: p, q => by
    show evalPoly σ π ρ (polyXor (polyMul p q) (q.map (monoMul m))) = _
    rw [evalPoly_polyXor, evalPoly_polyMul σ π ρ p q, evalPoly_map_monoMul]
    show _ = (xor (evalMono σ π ρ m) (evalPoly σ π ρ p) && evalPoly σ π ρ q)
    rw [xor_and_right, Bool.xor_comm]

-- ============================================================
-- Normalisation and the exact secret-freeness test
-- ============================================================

/-- Multilinear normal form of a model expression.  Total (structural
    recursion); worst-case exponential in size, so the *executable* checker
    wraps it with a size budget (rejecting on overflow — sound). -/
def toPoly : BExpr → Poly
  | .const false => []
  | .const true  => [[]]
  | .secret i    => [[PVar.secret i]]
  | .rand i      => [[PVar.rand i]]
  | .pub i       => [[PVar.pub i]]
  | .bxor a b    => polyXor (toPoly a) (toPoly b)
  | .band a b    => polyMul (toPoly a) (toPoly b)

/-- **Normalisation preserves semantics.** -/
theorem evalPoly_toPoly (σ π : Nat → Bool) (ρ : List Bool) :
    ∀ w : BExpr, evalPoly σ π ρ (toPoly w) = eval σ π ρ w
  | .const false => rfl
  | .const true  => by simp [toPoly, evalPoly, eval, evalMono]
  | .secret i    => by simp [toPoly, evalPoly, eval, evalMono, PVar.eval]
  | .rand i      => by simp [toPoly, evalPoly, eval, evalMono, PVar.eval]
  | .pub i       => by simp [toPoly, evalPoly, eval, evalMono, PVar.eval]
  | .bxor a b    => by
    show evalPoly σ π ρ (polyXor (toPoly a) (toPoly b)) = _
    rw [evalPoly_polyXor, evalPoly_toPoly σ π ρ a, evalPoly_toPoly σ π ρ b]
    rfl
  | .band a b    => by
    show evalPoly σ π ρ (polyMul (toPoly a) (toPoly b)) = _
    rw [evalPoly_polyMul, evalPoly_toPoly σ π ρ a, evalPoly_toPoly σ π ρ b]
    rfl

/-- The test: no surviving monomial contains a secret variable. -/
def polySecretFree (p : Poly) : Bool :=
  p.all (fun m => m.all (fun v => !v.isSecret))

/-- A secret-free polynomial evaluates independently of the secrets. -/
theorem evalPoly_congr_secret (π : Nat → Bool) (ρ : List Bool)
    (σ₁ σ₂ : Nat → Bool) :
    ∀ p : Poly, polySecretFree p = true →
      evalPoly σ₁ π ρ p = evalPoly σ₂ π ρ p := by
  have hvar : ∀ v : PVar, v.isSecret = false →
      PVar.eval σ₁ π ρ v = PVar.eval σ₂ π ρ v := by
    intro v hv; cases v <;> simp_all [PVar.isSecret, PVar.eval]
  have hmono : ∀ m : Mono, m.all (fun v => !v.isSecret) = true →
      evalMono σ₁ π ρ m = evalMono σ₂ π ρ m := by
    intro m hm
    induction m with
    | nil => rfl
    | cons v m ih =>
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                 Bool.not_true] at hm
      show (PVar.eval σ₁ π ρ v && evalMono σ₁ π ρ m) = _
      rw [hvar v hm.1, ih hm.2]
      rfl
  intro p hp
  induction p with
  | nil => rfl
  | cons m p ih =>
    simp only [polySecretFree, List.all_cons, Bool.and_eq_true] at hp
    show xor (evalMono σ₁ π ρ m) (evalPoly σ₁ π ρ p) = _
    rw [hmono m hp.1, ih hp.2]
    rfl

/-- **The verified exact acceptance test**: if the multilinear normal form of
    `w` has no secret in any surviving monomial, `w` is semantically
    secret-free.  This one test subsumes the tool's phase-2 syntactic check,
    its phase-3 budgeted ANF, *and* the factoring-certified acceptances (all
    are semantic-equality preserving, and only semantic freeness matters
    here). -/
theorem semSecretFree_of_polySecretFree (w : BExpr)
    (h : polySecretFree (toPoly w) = true) : SemSecretFree w := by
  intro σ₁ σ₂ π ρ
  rw [← evalPoly_toPoly σ₁ π ρ w, ← evalPoly_toPoly σ₂ π ρ w]
  exact evalPoly_congr_secret π ρ σ₁ σ₂ (toPoly w) h

end verif.Formal
