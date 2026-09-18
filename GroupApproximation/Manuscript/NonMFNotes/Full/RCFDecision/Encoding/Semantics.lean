import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SystemDefs

/-!
# Quantifier blocks and polynomial systems in prenex sentences

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding
`thm:mf-arithmetic`.  The sentence encoding `Φ(P,n,c)` has the shape
`∃ x_E ∀ x_A. (⋀ p = 0) ∧ (⋀ 0 ≤ q)`.  This file computes the truth of such
sentences:

* `pHolds_encExBlock`, `pHolds_encAllBlock`: a block of existential (universal)
  quantifiers over the variables of a list `L` is an existential (universal)
  quantifier over the assignments overriding `ρ` on `L` (`encOverride`);
* `qfHolds_encSystem`: the matrix `qfAnd [ps = 0] (nonnegQF qs)` holds iff every
  `p ∈ ps` vanishes and every `q ∈ qs` is nonnegative.
-/

namespace GroupApproximation.Full.NN11b

/-- The assignment that agrees with `σ` on the variables of `L` and with `ρ`
elsewhere. -/
def encOverride (L : List ℕ) (σ ρ : ℕ → ℝ) : ℕ → ℝ := fun j => if j ∈ L then σ j else ρ j

theorem encOverride_of_mem {L : List ℕ} {j : ℕ} (σ ρ : ℕ → ℝ) (h : j ∈ L) :
    encOverride L σ ρ j = σ j :=
  if_pos h

theorem encOverride_of_not_mem {L : List ℕ} {j : ℕ} (σ ρ : ℕ → ℝ) (h : j ∉ L) :
    encOverride L σ ρ j = ρ j :=
  if_neg h

theorem encOverride_nil (σ ρ : ℕ → ℝ) : encOverride [] σ ρ = ρ :=
  funext fun _ => if_neg List.not_mem_nil

/-- Absorbing an inner override into an outer one. -/
theorem encOverride_cons_override (i : ℕ) (L : List ℕ) (σ ρ : ℕ → ℝ) (r : ℝ) :
    encOverride (i :: L) (encOverride L σ (Function.update ρ i r)) ρ
      = encOverride L σ (Function.update ρ i r) := by
  funext j
  show (if j ∈ i :: L then (if j ∈ L then σ j else Function.update ρ i r j) else ρ j)
    = (if j ∈ L then σ j else Function.update ρ i r j)
  by_cases hj : j ∈ L
  · rw [if_pos (List.mem_cons_of_mem i hj)]
  · by_cases hji : j = i
    · rw [hji]
      have hm : i ∈ i :: L := List.mem_cons_self
      rw [if_pos hm]
    · have hm : j ∉ i :: L := fun h => (List.mem_cons.1 h).elim hji hj
      rw [if_neg hm, if_neg hj, Function.update_of_ne hji]

/-- Reading the value of the head variable off an override. -/
theorem encOverride_update_head (i : ℕ) (L : List ℕ) (σ ρ : ℕ → ℝ) :
    encOverride L σ (Function.update ρ i (σ i)) = encOverride (i :: L) σ ρ := by
  funext j
  show (if j ∈ L then σ j else Function.update ρ i (σ i) j)
    = (if j ∈ i :: L then σ j else ρ j)
  by_cases hj : j ∈ L
  · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
  · by_cases hji : j = i
    · rw [hji] at hj ⊢
      have hm : i ∈ i :: L := List.mem_cons_self
      rw [if_neg hj, if_pos hm, Function.update_self]
    · have hm : j ∉ i :: L := fun h => (List.mem_cons.1 h).elim hji hj
      rw [if_neg hj, if_neg hm, Function.update_of_ne hji]

/-- A block of existential quantifiers. -/
theorem pHolds_encExBlock (qs : List (Bool × ℕ)) (f : List (List Atom)) :
    ∀ (L : List ℕ) (ρ : ℕ → ℝ),
      PHolds (L.map (fun i => (true, i)) ++ qs) f ρ ↔
        ∃ σ : ℕ → ℝ, PHolds qs f (encOverride L σ ρ)
  | [], ρ => by
      show PHolds qs f ρ ↔ ∃ σ : ℕ → ℝ, PHolds qs f (encOverride [] σ ρ)
      constructor
      · intro h
        refine ⟨ρ, ?_⟩
        rw [encOverride_nil]
        exact h
      · rintro ⟨σ, h⟩
        rw [encOverride_nil] at h
        exact h
  | i :: L, ρ => by
      show (∃ r : ℝ, PHolds (L.map (fun i => (true, i)) ++ qs) f (Function.update ρ i r)) ↔
        ∃ σ : ℕ → ℝ, PHolds qs f (encOverride (i :: L) σ ρ)
      constructor
      · rintro ⟨r, h⟩
        obtain ⟨σ, hσ⟩ := (pHolds_encExBlock qs f L (Function.update ρ i r)).1 h
        refine ⟨encOverride L σ (Function.update ρ i r), ?_⟩
        rw [encOverride_cons_override]
        exact hσ
      · rintro ⟨σ, h⟩
        refine ⟨σ i, (pHolds_encExBlock qs f L (Function.update ρ i (σ i))).2 ⟨σ, ?_⟩⟩
        rw [encOverride_update_head]
        exact h

/-- A block of universal quantifiers in front of the quantifier-free matrix. -/
theorem pHolds_encAllBlock (f : List (List Atom)) :
    ∀ (L : List ℕ) (ρ : ℕ → ℝ),
      PHolds (L.map (fun i => (false, i))) f ρ ↔
        ∀ σ : ℕ → ℝ, qfHolds (encOverride L σ ρ) f
  | [], ρ => by
      show qfHolds ρ f ↔ ∀ σ : ℕ → ℝ, qfHolds (encOverride [] σ ρ) f
      constructor
      · intro h σ
        rw [encOverride_nil]
        exact h
      · intro h
        have h1 := h ρ
        rw [encOverride_nil] at h1
        exact h1
  | i :: L, ρ => by
      show (∀ r : ℝ, PHolds (L.map (fun i => (false, i))) f (Function.update ρ i r)) ↔
        ∀ σ : ℕ → ℝ, qfHolds (encOverride (i :: L) σ ρ) f
      constructor
      · intro h σ
        have h1 := (pHolds_encAllBlock f L (Function.update ρ i (σ i))).1 (h (σ i)) σ
        rw [encOverride_update_head] at h1
        exact h1
      · intro h r
        refine (pHolds_encAllBlock f L (Function.update ρ i r)).2 fun σ => ?_
        have h1 := h (encOverride L σ (Function.update ρ i r))
        rw [encOverride_cons_override] at h1
        exact h1

/-- An `∃ … ∃ ∀ … ∀` prefix. -/
theorem pHolds_encExAll (E A : List ℕ) (f : List (List Atom)) (ρ : ℕ → ℝ) :
    PHolds (E.map (fun i => (true, i)) ++ A.map (fun i => (false, i))) f ρ ↔
      ∃ σ : ℕ → ℝ, ∀ τ : ℕ → ℝ, qfHolds (encOverride A τ (encOverride E σ ρ)) f :=
  (pHolds_encExBlock (A.map (fun i => (false, i))) f E ρ).trans
    (exists_congr fun σ => pHolds_encAllBlock f A (encOverride E σ ρ))

/-- The conjunction `⋀ 0 ≤ q`. -/
theorem qfHolds_encNonneg (ρ : ℕ → ℝ) :
    ∀ qs : List MvP, qfHolds ρ (nonnegQF qs) ↔ ∀ q ∈ qs, 0 ≤ mvEval ρ q
  | [] => by
      show qfHolds ρ [[]] ↔ ∀ q ∈ ([] : List MvP), 0 ≤ mvEval ρ q
      constructor
      · intro _ q hq
        exact absurd hq List.not_mem_nil
      · intro _
        exact (qfHolds_cons ρ [] []).2 (Or.inl (guardHolds_nil ρ))
  | q :: qs => by
      show qfHolds ρ (qfAnd [[(true, q)], [(false, q)]] (nonnegQF qs)) ↔
        ∀ x ∈ q :: qs, 0 ≤ mvEval ρ x
      rw [qfHolds_and, qfHolds_encNonneg ρ qs, qfHolds_cons, qfHolds_cons,
        guardHolds_singleton, guardHolds_singleton, atomHolds_true, atomHolds_false,
        List.forall_mem_cons]
      constructor
      · rintro ⟨h1 | h1 | h1, h2⟩
        · exact ⟨le_of_lt h1, h2⟩
        · exact ⟨le_of_eq h1.symm, h2⟩
        · exact absurd h1 (qfHolds_nil ρ)
      · rintro ⟨h1, h2⟩
        exact ⟨(lt_or_eq_of_le h1).elim Or.inl fun h => Or.inr (Or.inl h.symm), h2⟩

/-- The conjunction `⋀ p = 0`, as one guard. -/
theorem guardHolds_encEqs (ρ : ℕ → ℝ) :
    ∀ ps : List MvP, guardHolds ρ (ps.map fun p => (false, p)) ↔ ∀ p ∈ ps, mvEval ρ p = 0
  | [] => by
      constructor
      · intro _ p hp
        exact absurd hp List.not_mem_nil
      · intro _
        exact guardHolds_nil ρ
  | p :: ps => by
      show guardHolds ρ ((false, p) :: ps.map fun p => (false, p)) ↔
        ∀ x ∈ p :: ps, mvEval ρ x = 0
      rw [guardHolds_cons, atomHolds_false, guardHolds_encEqs ρ ps, List.forall_mem_cons]

/-- The matrix of a polynomial system: equations and nonnegativity conditions. -/
theorem qfHolds_encSystem (ρ : ℕ → ℝ) (ps qs : List MvP) :
    qfHolds ρ (qfAnd [ps.map fun p => (false, p)] (nonnegQF qs)) ↔
      (∀ p ∈ ps, mvEval ρ p = 0) ∧ ∀ q ∈ qs, 0 ≤ mvEval ρ q := by
  rw [qfHolds_and, qfHolds_encNonneg, qfHolds_cons, guardHolds_encEqs]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact absurd h1 (qfHolds_nil ρ)
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inl h1, h2⟩

end GroupApproximation.Full.NN11b
