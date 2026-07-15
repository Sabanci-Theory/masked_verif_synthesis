namespace verif.Formal

/-!
# Uniform Tape Space — Probability Without Measure Theory

The random tape is a `List Bool` of length `n`; `allTapes n` enumerates all
`2^n` of them, each exactly once.  The "distribution" of an observable
`F : tape → α` is the *list of outcomes* `dist n F := (allTapes n).map F`;
two observables are identically distributed iff their outcome lists are
permutations of each other (equal multisets over the uniform tape space).
Probabilities are outcome counts over `allTapes n` — see
`List.Perm.countP_eq` for the bridge.

The engine of every soundness argument is `map_perm_allTapes`: a
length-preserving involution on tapes permutes `allTapes n`, so composing an
observable with it preserves the distribution.
-/

/-- All `2^n` tapes of length `n`. -/
def allTapes : Nat → List (List Bool)
  | 0     => [[]]
  | n + 1 => ((allTapes n).map (false :: ·)) ++ ((allTapes n).map (true :: ·))

theorem mem_allTapes : ∀ {n : Nat} {t : List Bool}, t ∈ allTapes n ↔ t.length = n := by
  intro n
  induction n with
  | zero => intro t; simp [allTapes, List.length_eq_zero_iff]
  | succ n ih =>
    intro t
    cases t with
    | nil => simp [allTapes]
    | cons b t' =>
      simp only [allTapes, List.mem_append, List.mem_map, ih, List.length_cons]
      cases b <;> simp [eq_comm]

/-- Auxiliary: counting a cons-tape in a cons-mapped tape list. -/
theorem count_map_cons (b c : Bool) (t' : List Bool) (l : List (List Bool)) :
    List.count (b :: t') (l.map (c :: ·)) = if b = c then List.count t' l else 0 := by
  rw [List.count_eq_countP, List.countP_map]
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl, List.count_eq_countP]
    apply List.countP_congr
    intro a _
    simp [Function.comp]
  · rw [if_neg hbc]
    apply List.countP_eq_zero.mpr
    intro a _
    simp [Function.comp]
    intro h
    exact absurd h.symm hbc

/-- Every length-`n` tape occurs exactly once in `allTapes n`. -/
theorem count_allTapes : ∀ (n : Nat) (t : List Bool), t.length = n →
    List.count t (allTapes n) = 1
  | 0, [], _ => by simp [allTapes]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, b :: t', h => by
    have ht' : t'.length = n := by simpa using h
    simp only [allTapes, List.count_append, count_map_cons]
    cases b <;> simp [count_allTapes n t' ht']

theorem count_allTapes_ne (n : Nat) (t : List Bool) (h : t.length ≠ n) :
    List.count t (allTapes n) = 0 :=
  List.count_eq_zero.mpr (fun hmem => h (mem_allTapes.mp hmem))

/-- **A length-preserving involution on tapes permutes `allTapes n`.**
    This is the measure-preservation step of the coupling argument: the
    bijection induced by one relabel `r ← e ⊕ r` permutes the uniform tape
    space. -/
theorem map_perm_allTapes {n : Nat} {f : List Bool → List Bool}
    (hlen : ∀ t : List Bool, t.length = n → (f t).length = n)
    (hinv : ∀ t : List Bool, t.length = n → f (f t) = t) :
    List.Perm ((allTapes n).map f) (allTapes n) := by
  rw [List.perm_iff_count]
  intro a
  rw [List.count_eq_countP, List.countP_map]
  by_cases ha : a.length = n
  · have h1 : List.countP ((fun x => x == a) ∘ f) (allTapes n)
        = List.count (f a) (allTapes n) := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro t ht
      have htn := mem_allTapes.mp ht
      simp only [Function.comp, beq_iff_eq]
      constructor
      · intro hfta; rw [← hfta, hinv t htn]
      · intro hta; rw [hta, hinv a ha]
    rw [h1, count_allTapes n (f a) (hlen a ha), count_allTapes n a ha]
  · have h1 : List.countP ((fun x => x == a) ∘ f) (allTapes n) = 0 := by
      apply List.countP_eq_zero.mpr
      intro t ht
      simp only [Function.comp, beq_iff_eq]
      intro hfta
      exact ha (hfta ▸ hlen t (mem_allTapes.mp ht))
    rw [h1, count_allTapes_ne n a ha]

-- ============================================================
-- Distributions as outcome lists
-- ============================================================

/-- The distribution of an observable `F` over the uniform length-`n` tapes:
    the multiset (as a list) of its outcomes. -/
def dist {α : Type} (n : Nat) (F : List Bool → α) : List α :=
  (allTapes n).map F

/-- Precomposing an observable with a length-preserving involution preserves
    its distribution. -/
theorem dist_perm_of_involution {α : Type} {n : Nat} {f : List Bool → List Bool}
    (hlen : ∀ t : List Bool, t.length = n → (f t).length = n)
    (hinv : ∀ t : List Bool, t.length = n → f (f t) = t)
    (F : List Bool → α) :
    List.Perm (dist n (fun ρ => F (f ρ))) (dist n F) := by
  have h : dist n (fun ρ => F (f ρ)) = ((allTapes n).map f).map F := by
    rw [List.map_map]; rfl
  rw [h]
  exact (map_perm_allTapes hlen hinv).map F

end verif.Formal
