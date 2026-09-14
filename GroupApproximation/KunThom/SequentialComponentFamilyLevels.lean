import GroupApproximation.KunThom.SequentialComponentFamilyCompletion
import GroupApproximation.Matching.ComponentClusterScale
import GroupApproximation.Matching.ComponentCompletedMultiplicativity
import GroupApproximation.Matching.Selection

/-!
# Level errors and good components of an expander decomposition

Fix an expander decomposition `D` of a sofic approximation `S` of `K` on the
generating set `T`, and an enumeration `enum : ℕ → K`.  The level-`k` error of a
component (`levelError`) collects

* the completed product failures of the pairs `(enum a, enum b)` with `a, b < k`;
* the completion disagreements of the labels in `T`;
* the ambient collisions of distinct labels in `T`;
* the local edit budget divided by the Cheeger constant.

A component is good at level `k` (`IsGoodAt`) when its edit budget is at most a
tenth of its Cheeger mass, `(k + 1)` times its level-`k` error is at most its
size, and `k` is below its size.  For each fixed `k` the mass of the components
that are not good is at most the sum of `badBound`, which is negligible
(`badBound_sum_negligible`).  `level D enum` is the diagonal level of
`Matching/Selection`: it tends to infinity (`level_diverges`), and the mass of
components that are not good at that level is still negligible
(`badMass_negligible`).

Every component carries one pruned set (`prunedSet`) from
`exists_pruned_completion`.  On a component whose budget is small, it removes at
most `2 B / h` points and leaves labels with directed Cheeger constant
`h / (8 |T|)`.  The removed mass on good components is negligible
(`prunedMass_negligible`).
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open scoped BigOperators

variable {K : Type} [Group K] {S : SoficApproximation K} {T : Finset K}
variable (D : ExpanderDecomposition S T)

/-! ### Pruned sets -/

theorem exists_componentPrune (hT : T.Nonempty) (n : ℕ) (C : D.componentIndex n) :
    ∃ U : Finset (indexedBlockModel (D.blocks n) C),
      10 * (D.componentLabelEditBudget n C : ℝ) ≤ D.cheeger * C.block.card →
        D.cheeger * U.card ≤ 2 * (D.componentLabelEditBudget n C : ℝ) ∧
          DirectedCoarea.HasCheegerLowerBound
            (finsetModel (indexedBlockModel (D.blocks n) C) (Finset.univ \ U))
            (T.image fun g ↦
              completion (Finset.univ \ U) (D.componentCompletedAction n C g))
            (D.cheeger / (8 * T.card)) := by
  by_cases hgood : 10 * (D.componentLabelEditBudget n C : ℝ) ≤ D.cheeger * C.block.card
  · have hedit : (((generatorGraph (indexedBlockModel (D.blocks n) C) T
        (D.componentCompletedAction n C)).editDistance (D.directIndexedComponentGraph n C)
          (Equiv.refl _) : ℕ) : ℝ) ≤ D.componentLabelEditBudget n C := by
      exact_mod_cast D.componentCompletedGraph_editDistance_le n C
    have hcardC : (Fintype.card (indexedBlockModel (D.blocks n) C) : ℝ) = C.block.card := by
      exact_mod_cast Fintype.card_coe C.block
    obtain ⟨U, hU, hcheeger⟩ := exists_pruned_completion T hT
      (D.componentCompletedAction n C) (D.directIndexedComponentGraph n C) (Equiv.refl _)
      (D.directIndexedComponentGraph_expands n C) (by rw [hcardC]; linarith)
    exact ⟨U, fun _ ↦ ⟨hU.trans (by linarith), hcheeger⟩⟩
  · exact ⟨∅, fun hsmall ↦ absurd hsmall hgood⟩

/-- The pruned set chosen on a component. -/
noncomputable def prunedSet (hT : T.Nonempty) (n : ℕ) (C : D.componentIndex n) :
    Finset (indexedBlockModel (D.blocks n) C) :=
  Classical.choose (exists_componentPrune D hT n C)

theorem prunedSet_spec (hT : T.Nonempty) (n : ℕ) (C : D.componentIndex n)
    (hgood : 10 * (D.componentLabelEditBudget n C : ℝ) ≤ D.cheeger * C.block.card) :
    D.cheeger * (prunedSet D hT n C).card ≤ 2 * (D.componentLabelEditBudget n C : ℝ) ∧
      DirectedCoarea.HasCheegerLowerBound
        (finsetModel (indexedBlockModel (D.blocks n) C) (Finset.univ \ prunedSet D hT n C))
        (T.image fun g ↦
          completion (Finset.univ \ prunedSet D hT n C) (D.componentCompletedAction n C g))
        (D.cheeger / (8 * T.card)) :=
  Classical.choose_spec (exists_componentPrune D hT n C) hgood

theorem card_prunedSet_le (hT : T.Nonempty) (n : ℕ) (C : D.componentIndex n)
    (hgood : 10 * (D.componentLabelEditBudget n C : ℝ) ≤ D.cheeger * C.block.card) :
    ((prunedSet D hT n C).card : ℝ) ≤
      2 * (D.cheeger⁻¹ * D.componentLabelEditBudget n C) := by
  have h := (prunedSet_spec D hT n C hgood).1
  have hc := D.cheeger_pos
  have hinv : D.cheeger⁻¹ * D.cheeger = 1 := inv_mul_cancel₀ hc.ne'
  calc ((prunedSet D hT n C).card : ℝ) =
        D.cheeger⁻¹ * (D.cheeger * (prunedSet D hT n C).card) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ D.cheeger⁻¹ * (2 * (D.componentLabelEditBudget n C : ℝ)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
    _ = 2 * (D.cheeger⁻¹ * D.componentLabelEditBudget n C) := by ring

/-! ### Level errors -/

/-- Points of a component where two ambient labels collide. -/
noncomputable def componentCollision (n : ℕ) (C : D.componentIndex n) (s t : K) :
    Finset (indexedBlockModel (D.blocks n) C) :=
  Finset.univ.filter fun x ↦ S.map n s (x : S.model n) = S.map n t (x : S.model n)

/-- Completed product failures of the enumerated pairs below level `k`. -/
noncomputable def multError (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n) : ℝ :=
  ∑ p ∈ Finset.range k ×ˢ Finset.range k,
    ((D.componentMultiplicationError n C (enum p.1) (enum p.2)).card : ℝ)

/-- Completion disagreements of the labels. -/
noncomputable def disError (n : ℕ) (C : D.componentIndex n) : ℝ :=
  ∑ t ∈ T, ((D.componentCompletionDisagreement n C t).card : ℝ)

open Classical in
/-- Ambient collisions of distinct labels. -/
noncomputable def collError (n : ℕ) (C : D.componentIndex n) : ℝ :=
  ∑ p ∈ T.offDiag, ((componentCollision D n C p.1 p.2).card : ℝ)

/-- The level-`k` error of a component. -/
noncomputable def levelError (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n) : ℝ :=
  multError D enum k n C + disError D n C + collError D n C +
    D.cheeger⁻¹ * D.componentLabelEditBudget n C

theorem budget_div_nonneg (n : ℕ) (C : D.componentIndex n) :
    0 ≤ D.cheeger⁻¹ * (D.componentLabelEditBudget n C : ℝ) :=
  mul_nonneg (inv_nonneg.mpr D.cheeger_pos.le) (Nat.cast_nonneg _)

theorem levelError_nonneg (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n) :
    0 ≤ levelError D enum k n C := by
  have h1 : 0 ≤ multError D enum k n C := by
    unfold multError
    exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have h2 : 0 ≤ disError D n C := by
    unfold disError
    exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have h3 : 0 ≤ collError D n C := by
    unfold collError
    exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have h4 := budget_div_nonneg D n C
  unfold levelError
  linarith

theorem multError_sum_negligible (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) (k : ℕ) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n, multError D enum k n C) := by
  refine Negligible.congr (Negligible.sum (Finset.range k ×ˢ Finset.range k)
    (fun p n ↦ ∑ C : D.componentIndex n,
      ((D.componentMultiplicationError n C (enum p.1) (enum p.2)).card : ℝ))
    (fun p _ ↦ D.componentMultiplicationError_sum_negligible hsymm hgen
      (enum p.1) (enum p.2))) (fun n ↦ ?_)
  unfold multError
  exact Finset.sum_comm

theorem disError_sum_negligible (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n, disError D n C) := by
  refine Negligible.congr (Negligible.sum T
    (fun t n ↦ ∑ C : D.componentIndex n,
      ((D.componentCompletionDisagreement n C t).card : ℝ))
    (fun t _ ↦ ?_)) (fun n ↦ ?_)
  · simpa only [ExpanderDecomposition.componentCompletionDisagreement] using
      D.componentCompletedAction_disagreement_sum_negligible hsymm hgen t
  · unfold disError
    exact Finset.sum_comm

theorem collError_sum_negligible :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n, collError D n C) := by
  classical
  refine Negligible.congr (Negligible.sum T.offDiag
    (fun p n ↦ ((S.collisionError n p.1 p.2).card : ℝ))
    (fun p hp ↦ S.collisionError_negligible p.1 p.2 (Finset.mem_offDiag.mp hp).2.2))
    (fun n ↦ ?_)
  unfold collError
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  exact (BlockIndex.sum_card_filter (D.blocks n)
    (fun x ↦ S.map n p.1 x = S.map n p.2 x)).symm

theorem budget_sum_negligible :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        D.cheeger⁻¹ * (D.componentLabelEditBudget n C : ℝ)) := by
  refine Negligible.congr
    (Negligible.const_mul D.cheeger⁻¹ D.componentLabelEditBudget_sum_negligible)
    (fun n ↦ ?_)
  exact Finset.mul_sum _ _ _

theorem levelError_sum_negligible (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) (k : ℕ) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n, levelError D enum k n C) := by
  refine Negligible.congr ((((multError_sum_negligible D hsymm hgen enum k).add
    (disError_sum_negligible D hsymm hgen)).add (collError_sum_negligible D)).add
      (budget_sum_negligible D)) (fun n ↦ ?_)
  simp only [levelError, Finset.sum_add_distrib]

/-! ### Good components -/

/-- A component is good at level `k`. -/
def IsGoodAt (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n) : Prop :=
  10 * (D.componentLabelEditBudget n C : ℝ) ≤ D.cheeger * C.block.card ∧
    ((k : ℝ) + 1) * levelError D enum k n C ≤ C.block.card ∧ k < C.block.card

/-- A majorant for the mass of a component that is not good at level `k`. -/
noncomputable def badBound (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n) : ℝ :=
  10 * (D.cheeger⁻¹ * D.componentLabelEditBudget n C) +
    ((k : ℝ) + 1) * levelError D enum k n C +
      if (C.block.card : ℝ) ≤ k then (C.block.card : ℝ) else 0

theorem badBound_nonneg (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n) :
    0 ≤ badBound D enum k n C := by
  have hE := levelError_nonneg D enum k n C
  have hB := budget_div_nonneg D n C
  have hEk : 0 ≤ ((k : ℝ) + 1) * levelError D enum k n C :=
    mul_nonneg (by positivity) hE
  have hind : (0 : ℝ) ≤ if (C.block.card : ℝ) ≤ k then (C.block.card : ℝ) else 0 := by
    split_ifs <;> positivity
  unfold badBound
  linarith

theorem mass_le_badBound (enum : ℕ → K) (k n : ℕ) (C : D.componentIndex n)
    (hC : ¬ IsGoodAt D enum k n C) :
    (C.block.card : ℝ) ≤ badBound D enum k n C := by
  have hE := levelError_nonneg D enum k n C
  have hB := budget_div_nonneg D n C
  have hEk : 0 ≤ ((k : ℝ) + 1) * levelError D enum k n C :=
    mul_nonneg (by positivity) hE
  have hind : (0 : ℝ) ≤ if (C.block.card : ℝ) ≤ k then (C.block.card : ℝ) else 0 := by
    split_ifs <;> positivity
  unfold badBound
  by_cases h1 : 10 * (D.componentLabelEditBudget n C : ℝ) ≤ D.cheeger * C.block.card
  · by_cases h2 : ((k : ℝ) + 1) * levelError D enum k n C ≤ C.block.card
    · have h3 : ¬ k < C.block.card := fun h3 ↦ hC ⟨h1, h2, h3⟩
      have h4 : (C.block.card : ℝ) ≤ k := by exact_mod_cast not_lt.mp h3
      rw [if_pos h4]
      linarith
    · have h5 := not_le.mp h2
      linarith
  · have hc := D.cheeger_pos
    have h5 := not_le.mp h1
    have hinv : D.cheeger⁻¹ * D.cheeger = 1 := inv_mul_cancel₀ hc.ne'
    have h6 : (C.block.card : ℝ) ≤ 10 * (D.cheeger⁻¹ * D.componentLabelEditBudget n C) := by
      calc (C.block.card : ℝ) = D.cheeger⁻¹ * (D.cheeger * C.block.card) := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ D.cheeger⁻¹ * (10 * (D.componentLabelEditBudget n C : ℝ)) :=
            mul_le_mul_of_nonneg_left h5.le (inv_nonneg.mpr hc.le)
        _ = 10 * (D.cheeger⁻¹ * D.componentLabelEditBudget n C) := by ring
    linarith

theorem badBound_sum_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) (k : ℕ) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n, badBound D enum k n C) := by
  have hb := Negligible.const_mul 10 (budget_sum_negligible D)
  have he := Negligible.const_mul ((k : ℝ) + 1) (levelError_sum_negligible D hsymm hgen enum k)
  have hs := D.smallBlockVertices_negligible hsymm hgen k
  refine Negligible.congr ((hb.add he).add hs) (fun n ↦ ?_)
  simp only [badBound, Finset.sum_add_distrib, Finset.mul_sum]
  rw [sum_smallBlock_card]

/-! ### The diagonal level -/

/-- The doubly indexed error array of the diagonal choice. -/
noncomputable def levelArray (enum : ℕ → K) (n k : ℕ) : ℝ :=
  (∑ C : D.componentIndex n, badBound D enum k n C) / Fintype.card (S.model n)

theorem levelArray_nonneg (enum : ℕ → K) (n k : ℕ) : 0 ≤ levelArray D enum n k := by
  unfold levelArray
  exact div_nonneg (Finset.sum_nonneg fun C _ ↦ badBound_nonneg D enum k n C)
    (Nat.cast_nonneg _)

theorem levelArray_vanishing [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) (k : ℕ) :
    Vanishing fun n ↦ levelArray D enum n k :=
  badBound_sum_negligible D hsymm hgen enum k

/-- The diagonal level: it diverges while the bad mass at that level stays
negligible. -/
noncomputable def level (enum : ℕ → K) (n : ℕ) : ℕ :=
  diagonalLevel (levelArray D enum) n

theorem level_diverges [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → k ≤ level D enum n :=
  diagonalLevel_diverges (levelArray D enum) (levelArray_vanishing D hsymm hgen enum)

theorem levelArray_level_vanishing [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) :
    Vanishing fun n ↦ levelArray D enum n (level D enum n) :=
  diagonalLevel_error (levelArray D enum) (levelArray_nonneg D enum)
    (levelArray_vanishing D hsymm hgen enum)

open Classical in
/-- Mass of the components that are not good at the diagonal level. -/
noncomputable def badMass (enum : ℕ → K) (n : ℕ) : ℝ :=
  ∑ C : D.componentIndex n,
    if IsGoodAt D enum (level D enum n) n C then 0 else (C.block.card : ℝ)

theorem badMass_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) (badMass D enum) := by
  refine Vanishing.squeeze (fun n ↦ div_nonneg ?_ (Nat.cast_nonneg _)) (fun n ↦ ?_)
    (levelArray_level_vanishing D hsymm hgen enum)
  · unfold badMass
    exact Finset.sum_nonneg fun C _ ↦ by split_ifs <;> positivity
  · unfold levelArray
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    unfold badMass
    refine Finset.sum_le_sum fun C _ ↦ ?_
    split_ifs with hC
    · exact badBound_nonneg D enum _ n C
    · exact mass_le_badBound D enum _ n C hC

open Classical in
/-- Mass removed by pruning the good components at the diagonal level. -/
noncomputable def prunedMass (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) : ℝ :=
  ∑ C : D.componentIndex n,
    if IsGoodAt D enum (level D enum n) n C then ((prunedSet D hT n C).card : ℝ) else 0

theorem prunedMass_negligible (hT : T.Nonempty) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) (prunedMass D hT enum) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (fun n ↦ ?_)
    (Negligible.const_mul 2 (budget_sum_negligible D))
  · unfold prunedMass
    exact Finset.sum_nonneg fun C _ ↦ by split_ifs <;> positivity
  · unfold prunedMass
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun C _ ↦ ?_
    split_ifs with hC
    · exact card_prunedSet_le D hT n C hC.1
    · exact mul_nonneg (by norm_num) (budget_div_nonneg D n C)

end SequentialComponentFamily
end GroupApproximation
