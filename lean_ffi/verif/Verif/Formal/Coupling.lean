import Verif.Formal.Model
import Verif.Formal.Tape

namespace verif.Formal

open BExpr

/-!
# Coupling Soundness — the Optimistic-Sampling Theorem Chain

The formal counterpart of the engine's derivation: a coupling is a list of
relabels `r ← e ⊕ r` (side condition: `e` does not mention `r`, and `r` lies
inside the tape).  Each step induces a length-preserving involution on the
random tape (`flipTape`), so it preserves the joint distribution of any
expression tuple (`dist_substStep_perm`); composing the steps gives the same
for a whole coupling (`dist_applyCoupling_perm`).

**Main theorem** (`coupling_blinds`): if a valid coupling `T` maps every
expression of a tuple `ws` to a *semantically secret-free* image, then the
joint distribution of `ws` is independent of the secrets.  This is exactly
the certificate the tool's `checkProbeCompleteT` + `couplingExtend` produce:
`ws` = chosen probe ++ extension candidates, `T` = the recorded substitution
list.  Marginalisation (`indep_select`) then covers every subset of the safe
set, of any size and in any order — the justification for the coupling-driven
probe-set extension.
-/

/-- Joint evaluation of a tuple of expressions on one tape. -/
def evalTuple (σ π : Nat → Bool) (ws : List BExpr) (ρ : List Bool) : List Bool :=
  ws.map (eval σ π ρ)

/-- The security property: the joint outcome distribution of `ws` over the
    uniform length-`n` tape is the same for every pair of secret assignments
    (with the public inputs held fixed — i.e. conditioned on publics). -/
def IndepOfSecrets (n : Nat) (ws : List BExpr) : Prop :=
  ∀ σ₁ σ₂ π : Nat → Bool,
    List.Perm (dist n (evalTuple σ₁ π ws)) (dist n (evalTuple σ₂ π ws))

-- ============================================================
-- One step: the tape involution induced by `r ← e ⊕ r`
-- ============================================================

/-- The tape map induced by the relabel `r ← e ⊕ r`: flip position `r` by
    `e`'s value.  (`List.set` out of range is the identity.) -/
def flipTape (σ π : Nat → Bool) (r : Nat) (e : BExpr) (ρ : List Bool) : List Bool :=
  ρ.set r (xor (eval σ π ρ e) (ρ.getD r false))

theorem length_flipTape (σ π : Nat → Bool) (r : Nat) (e : BExpr) (ρ : List Bool) :
    (flipTape σ π r e ρ).length = ρ.length :=
  List.length_set

/-- `e` evaluates identically on the flipped tape — only position `r` changed
    and `e` does not mention it. -/
theorem eval_flipTape (σ π : Nat → Bool) (r : Nat) (e : BExpr) (ρ : List Bool)
    (hm : mentionsRand e r = false) :
    eval σ π (flipTape σ π r e ρ) e = eval σ π ρ e := by
  apply eval_congr_rand
  intro i hi
  have hir : r ≠ i := by
    intro h; subst h; simp [hm] at hi
  unfold flipTape
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hir]

private theorem xor_xor_cancel (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

/-- The flip is an involution (for any tape; out of range it is the identity
    twice). -/
theorem flipTape_involutive (σ π : Nat → Bool) (r : Nat) (e : BExpr) (ρ : List Bool)
    (hm : mentionsRand e r = false) :
    flipTape σ π r e (flipTape σ π r e ρ) = ρ := by
  have hev := eval_flipTape σ π r e ρ hm
  apply List.ext_getElem?
  intro j
  by_cases hj : r = j
  · subst hj
    by_cases hr : r < ρ.length
    · have hr' : r < (flipTape σ π r e ρ).length := by rw [length_flipTape]; exact hr
      show ((flipTape σ π r e ρ).set r _)[r]? = ρ[r]?
      rw [List.getElem?_set_self hr', hev]
      have hgetD : (flipTape σ π r e ρ).getD r false = xor (eval σ π ρ e) (ρ.getD r false) := by
        unfold flipTape
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hr]
        rfl
      rw [hgetD, xor_xor_cancel, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hr]
      rfl
    · have h1 : ρ.length ≤ r := Nat.le_of_not_lt hr
      have h2 : (flipTape σ π r e ρ).length ≤ r := by rw [length_flipTape]; exact h1
      show ((flipTape σ π r e ρ).set r _)[r]? = ρ[r]?
      rw [List.getElem?_eq_none (by rw [List.length_set]; exact h2),
          List.getElem?_eq_none h1]
  · show ((flipTape σ π r e ρ).set r _)[j]? = ρ[j]?
    rw [List.getElem?_set_ne hj]
    unfold flipTape
    rw [List.getElem?_set_ne hj]

-- ============================================================
-- One step: distribution preservation
-- ============================================================

/-- One coupling step on a tuple: substitute `r ← e ⊕ r` in every component.
    This is the formal counterpart of the engine's `substTuple` (which
    substitutes `r ← x₁` with `x₁ = e ⊕ r` interned; semantically equal). -/
def substStep (r : Nat) (e : BExpr) (ws : List BExpr) : List BExpr :=
  ws.map (substR r (bxor e (rand r)))

/-- Substituted tuple at `ρ` = original tuple at the flipped tape. -/
theorem evalTuple_substStep (σ π : Nat → Bool) (ρ : List Bool) (r : Nat) (e : BExpr)
    (ws : List BExpr) (hr : r < ρ.length) :
    evalTuple σ π (substStep r e ws) ρ = evalTuple σ π ws (flipTape σ π r e ρ) := by
  unfold evalTuple substStep
  rw [List.map_map]
  apply List.map_congr_left
  intro w _
  show eval σ π ρ (substR r (bxor e (rand r)) w) = _
  rw [eval_substR σ π ρ r _ hr w]
  rfl

/-- **One-step optimistic sampling**: a single valid relabel `r ← e ⊕ r`
    preserves the joint distribution of any tuple. -/
theorem dist_substStep_perm (n : Nat) (σ π : Nat → Bool) (r : Nat) (e : BExpr)
    (ws : List BExpr) (hr : r < n) (hm : mentionsRand e r = false) :
    List.Perm (dist n (evalTuple σ π (substStep r e ws)))
              (dist n (evalTuple σ π ws)) := by
  have heq : dist n (evalTuple σ π (substStep r e ws))
      = dist n (fun ρ => evalTuple σ π ws (flipTape σ π r e ρ)) := by
    unfold dist
    apply List.map_congr_left
    intro t ht
    exact evalTuple_substStep σ π t r e ws (by rw [mem_allTapes.mp ht]; exact hr)
  rw [heq]
  exact dist_perm_of_involution
    (fun t htn => by rw [length_flipTape]; exact htn)
    (fun t _ => flipTape_involutive σ π r e t hm)
    (evalTuple σ π ws)

-- ============================================================
-- Whole couplings
-- ============================================================

/-- A coupling certificate: ordered relabels `(r, e)`, each meaning
    `r ← e ⊕ r`, applied left to right (the engine's recording and replay
    order). -/
abbrev Coupling := List (Nat × BExpr)

/-- Validity of a certificate against tape length `n`: each step's random is
    on the tape and its context does not mention it.  These are exactly the
    side conditions the engine's `findSimpleRandom`/`findGeneralRandom`
    establish — but the verified checker re-checks them, so the engine need
    not be trusted. -/
def ValidCoupling (n : Nat) (T : Coupling) : Prop :=
  ∀ p ∈ T, p.1 < n ∧ mentionsRand p.2 p.1 = false

/-- Apply a whole coupling to a tuple, first step first (the replay order of
    `couplingExtend`). -/
def applyCoupling (T : Coupling) (ws : List BExpr) : List BExpr :=
  T.foldl (fun ws p => substStep p.1 p.2 ws) ws

/-- A valid coupling preserves the joint distribution of any tuple. -/
theorem dist_applyCoupling_perm {n : Nat} :
    ∀ (T : Coupling), ValidCoupling n T → ∀ (σ π : Nat → Bool) (ws : List BExpr),
      List.Perm (dist n (evalTuple σ π (applyCoupling T ws)))
                (dist n (evalTuple σ π ws))
  | [], _, _, _, _ => List.Perm.refl _
  | p :: T, hT, σ, π, ws =>
    have hp := hT p List.mem_cons_self
    have hT' : ValidCoupling n T := fun q hq => hT q (List.mem_cons_of_mem p hq)
    (dist_applyCoupling_perm T hT' σ π (substStep p.1 p.2 ws)).trans
      (dist_substStep_perm n σ π p.1 p.2 ws hp.1 hp.2)

-- ============================================================
-- Main theorem
-- ============================================================

/-- **Coupling soundness.**  If a valid coupling maps every component of `ws`
    to a semantically secret-free image, the joint distribution of `ws` is
    independent of the secrets.

    This is the statement certified by the tool per accepted probe region:
    `ws` is the chosen probe tuple together with every extension candidate the
    replay blinds, and `T` is the recorded derivation.  Note the hypothesis is
    *semantic* freeness of the images: syntactic freeness
    (`coupling_blinds_syntactic`) and polynomial-normal-form freeness
    (Phase 2) both imply it, which is what lets the verified checker accept
    factoring- and ANF-certified discharges. -/
theorem coupling_blinds {n : Nat} {T : Coupling} {ws : List BExpr}
    (hT : ValidCoupling n T)
    (hfree : ∀ w ∈ applyCoupling T ws, SemSecretFree w) :
    IndepOfSecrets n ws := by
  intro σ₁ σ₂ π
  have hmid : dist n (evalTuple σ₁ π (applyCoupling T ws))
      = dist n (evalTuple σ₂ π (applyCoupling T ws)) := by
    unfold dist
    apply List.map_congr_left
    intro t _
    unfold evalTuple
    apply List.map_congr_left
    intro w hw
    exact hfree w hw σ₁ σ₂ π t
  have h1 := (dist_applyCoupling_perm T hT σ₁ π ws).symm
  rw [hmid] at h1
  exact h1.trans (dist_applyCoupling_perm T hT σ₂ π ws)

/-- Corollary with the syntactic acceptance test (the tool's phase-2
    `tupleHasSecret`). -/
theorem coupling_blinds_syntactic {n : Nat} {T : Coupling} {ws : List BExpr}
    (hT : ValidCoupling n T)
    (hfree : ∀ w ∈ applyCoupling T ws, hasSecret w = false) :
    IndepOfSecrets n ws :=
  coupling_blinds hT (fun w hw => semSecretFree_of_not_hasSecret w (hfree w hw))

-- ============================================================
-- Marginalisation: subsets of a certified tuple stay independent
-- ============================================================

/-- Project an outcome onto the positions `is`. -/
def selectIdx (is : List Nat) (out : List Bool) : List Bool :=
  is.map (fun i => out.getD i false)

/-- **Marginalisation.**  Any selection (subset, reordering, or repetition)
    of the components of a jointly independent tuple is itself independent
    of the secrets.  Combined with `coupling_blinds` on the whole safe set,
    this covers every ≤ d probe subset drawn from it — the soundness of the
    coupling-driven probe-set extension. -/
theorem indep_select {n : Nat} {ws : List BExpr} (h : IndepOfSecrets n ws)
    (is : List Nat) (his : ∀ i ∈ is, i < ws.length) :
    IndepOfSecrets n (is.map (fun i => ws.getD i (BExpr.const false))) := by
  intro σ₁ σ₂ π
  have key : ∀ (σ : Nat → Bool) (ρ : List Bool),
      evalTuple σ π (is.map (fun i => ws.getD i (BExpr.const false))) ρ
        = selectIdx is (evalTuple σ π ws ρ) := by
    intro σ ρ
    unfold evalTuple selectIdx
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    show eval σ π ρ (ws.getD i (BExpr.const false))
      = (ws.map (eval σ π ρ)).getD i false
    simp [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (his i hi)]
  have e1 : ∀ σ : Nat → Bool,
      dist n (evalTuple σ π (is.map (fun i => ws.getD i (BExpr.const false))))
        = (dist n (evalTuple σ π ws)).map (selectIdx is) := by
    intro σ
    unfold dist
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    exact key σ t
  rw [e1 σ₁, e1 σ₂]
  exact (h σ₁ σ₂ π).map (selectIdx is)

/-- Every sublist of `ws` arises by selecting positions of `ws`. -/
theorem sublist_eq_select {probe ws : List BExpr} (h : probe.Sublist ws) :
    ∃ is : List Nat, (∀ i ∈ is, i < ws.length)
      ∧ probe = is.map (fun i => ws.getD i (BExpr.const false)) := by
  induction h with
  | slnil => exact ⟨[], by simp, rfl⟩
  | cons a h ih =>
    obtain ⟨is, hb, rfl⟩ := ih
    refine ⟨is.map (· + 1), ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      simpa using hb j hj
    · rw [List.map_map]
      apply List.map_congr_left
      intro i _
      rfl
  | cons_cons a h ih =>
    obtain ⟨is, hb, rfl⟩ := ih
    refine ⟨0 :: is.map (· + 1), ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with h0 | hmem
      · subst h0; simp
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
        simpa using hb j hj
    · simp only [List.map_cons, List.map_map]
      rfl

/-- **Subset soundness**: every sublist (probe subset) of a jointly
    independent tuple is independent of the secrets. -/
theorem sublist_indep {n : Nat} {ws probe : List BExpr}
    (h : IndepOfSecrets n ws) (hsub : probe.Sublist ws) :
    IndepOfSecrets n probe := by
  obtain ⟨is, hb, rfl⟩ := sublist_eq_select hsub
  exact indep_select h is hb

/-- Any probe list whose elements are drawn from a jointly independent tuple
    (in any order, with any multiplicity) arises as an index selection. -/
theorem mem_eq_select {ws : List BExpr} :
    ∀ (probe : List BExpr), (∀ w ∈ probe, w ∈ ws) →
      ∃ is : List Nat, (∀ i ∈ is, i < ws.length)
        ∧ probe = is.map (fun i => ws.getD i (BExpr.const false))
  | [], _ => ⟨[], fun _ hi => (nomatch hi), rfl⟩
  | w :: probe, h => by
    obtain ⟨is, hb, hmap⟩ :=
      mem_eq_select probe (fun v hv => h v (List.mem_cons_of_mem w hv))
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (h w List.mem_cons_self)
    refine ⟨i :: is, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with h0 | hmem
      · subst h0; exact hi
      · exact hb j hmem
    · rw [List.map_cons, ← hmap]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hget]
      rfl

/-- **Member soundness**: any probe drawn from a jointly independent tuple —
    any subset, in any order, with repetitions — is independent of the
    secrets.  This is the strongest reusable form: it absorbs all the
    order/multiplicity bookkeeping of the probe-space search. -/
theorem mem_indep {n : Nat} {ws probe : List BExpr}
    (h : IndepOfSecrets n ws) (hmem : ∀ w ∈ probe, w ∈ ws) :
    IndepOfSecrets n probe := by
  obtain ⟨is, hb, rfl⟩ := mem_eq_select probe hmem
  exact indep_select h is hb

/-- Readable corollary: for every fixed outcome, the *number of tapes* on
    which the tuple takes that outcome does not depend on the secrets —
    i.e. `Pr[ws = out]` is secret-independent. -/
theorem indep_count {n : Nat} {ws : List BExpr} (h : IndepOfSecrets n ws)
    (σ₁ σ₂ π : Nat → Bool) (out : List Bool) :
    (allTapes n).countP (fun ρ => evalTuple σ₁ π ws ρ == out)
      = (allTapes n).countP (fun ρ => evalTuple σ₂ π ws ρ == out) := by
  have hc := (h σ₁ σ₂ π).countP_eq (fun o => o == out)
  simp only [dist, List.countP_map, Function.comp_def] at hc
  exact hc

end verif.Formal
