import GroupApproximation.Matching.ComponentCompletedMultiplicativity

/-!
# The total completed component action

The disjoint union of the distinct expander blocks is canonically equivalent
to the ambient finite model.  Acting by the chosen completion separately on
each block therefore gives one permutation of a finite model.  This file
packages that construction and identifies its global identity and product
error counts with the componentwise sums already proved negligible.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- Disjoint union of the distinct indexed components at one finite stage. -/
noncomputable def completedComponentModel (n : ℕ) : FiniteModel where
  carrier := Σ C : D.componentIndex n, indexedBlockModel (D.blocks n) C
  fintype := inferInstance
  decidableEq := Classical.decEq _

/-- Forgetting the component tag identifies the component disjoint union
with the original finite model. -/
noncomputable def completedComponentEquiv (n : ℕ) :
    D.completedComponentModel n ≃ S.model n := by
  let forget : D.completedComponentModel n → S.model n := fun x ↦ x.2.1
  apply Equiv.ofBijective forget
  constructor
  · rintro ⟨C, x⟩ ⟨E, y⟩ hxy
    change (x : S.model n) = (y : S.model n) at hxy
    have hCE : C = E := by
      by_contra hne
      have hd := BlockIndex.pairwise_disjoint (D.blocks n)
        (Finset.mem_univ C) (Finset.mem_univ E) hne
      have hxE : (x : S.model n) ∈ E.block := by
        rw [hxy]
        exact y.2
      exact Finset.disjoint_left.mp hd x.2 hxE
    subst E
    have : x = y := Subtype.ext hxy
    subst y
    rfl
  · intro y
    let C : D.componentIndex n :=
      ⟨(D.blocks n).block y,
        (D.blocks n).block_mem_blocksFinset y⟩
    let x : indexedBlockModel (D.blocks n) C :=
      ⟨y, (D.blocks n).self_mem y⟩
    exact ⟨⟨C, x⟩, rfl⟩

@[simp] theorem completedComponentEquiv_apply (n : ℕ)
    (x : D.completedComponentModel n) :
    D.completedComponentEquiv n x = x.2.1 := rfl

/-- The completed permutation acting independently on every component. -/
noncomputable def completedComponentPerm (n : ℕ) (g : G) :
    Equiv.Perm (D.completedComponentModel n) :=
  Equiv.Perm.sigmaCongrRight fun C ↦ D.componentCompletedAction n C g

@[simp] theorem completedComponentPerm_apply (n : ℕ) (g : G)
    (x : D.completedComponentModel n) :
    D.completedComponentPerm n g x =
      ⟨x.1, D.componentCompletedAction n x.1 g x.2⟩ := rfl

/-- The disjoint component model has exactly the ambient model cardinality. -/
theorem card_completedComponentModel (n : ℕ) :
    Fintype.card (D.completedComponentModel n) =
      Fintype.card (S.model n) :=
  Fintype.card_congr (D.completedComponentEquiv n)

/-- The global product-error count of the total completed permutation is the
sum of the product-error counts on the individual components. -/
theorem card_completedComponentPerm_multiplicationError
    (n : ℕ) (g h : G) :
    (hammingDisagreement (D.completedComponentPerm n (g * h))
      (D.completedComponentPerm n g * D.completedComponentPerm n h)).card =
      ∑ C : D.componentIndex n,
        (D.componentMultiplicationError n C g h).card := by
  classical
  unfold hammingDisagreement componentMultiplicationError
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ a : (Σ C : D.componentIndex n,
      indexedBlockModel (D.blocks n) C),
        if D.completedComponentPerm n (g * h) a ≠
          (D.completedComponentPerm n g * D.completedComponentPerm n h) a
        then 1 else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [completedComponentPerm_apply, Equiv.Perm.mul_apply]
  have hsigma_iff :
      ((show D.completedComponentModel n from
          ⟨C, D.componentCompletedAction n C (g * h) x⟩) =
        (show D.completedComponentModel n from
          ⟨C, D.componentCompletedAction n C g
            (D.componentCompletedAction n C h x)⟩)) ↔
      D.componentCompletedAction n C (g * h) x =
        D.componentCompletedAction n C g
          (D.componentCompletedAction n C h x) := by
    constructor
    · intro hsigma
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
    · intro heq
      exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq heq⟩
  by_cases heq : D.componentCompletedAction n C (g * h) x =
      D.componentCompletedAction n C g
        (D.componentCompletedAction n C h x)
  · have hsigma := hsigma_iff.mpr heq
    rw [if_neg (fun hne ↦ hne hsigma), if_neg (fun hne ↦ hne heq)]
  · have hsigma :
        (show D.completedComponentModel n from
          ⟨C, D.componentCompletedAction n C (g * h) x⟩) ≠
        (show D.completedComponentModel n from
          ⟨C, D.componentCompletedAction n C g
            (D.componentCompletedAction n C h x)⟩) :=
      fun hs ↦ heq (hsigma_iff.mp hs)
    rw [if_pos hsigma, if_pos heq]

/-- The global identity-error count of the total completed permutation is
the sum of the identity-error counts on the individual components. -/
theorem card_completedComponentPerm_identityError (n : ℕ) :
    (hammingDisagreement (D.completedComponentPerm n (1 : G)) 1).card =
      ∑ C : D.componentIndex n,
        (D.componentIdentityError n C).card := by
  classical
  unfold hammingDisagreement componentIdentityError
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ a : (Σ C : D.componentIndex n,
      indexedBlockModel (D.blocks n) C),
        if D.completedComponentPerm n (1 : G) a ≠
          (1 : Equiv.Perm (D.completedComponentModel n)) a
        then 1 else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [completedComponentPerm_apply, Equiv.Perm.one_apply]
  have hsigma_iff :
      ((show D.completedComponentModel n from
          ⟨C, D.componentCompletedAction n C (1 : G) x⟩) =
        (show D.completedComponentModel n from ⟨C, x⟩)) ↔
      D.componentCompletedAction n C (1 : G) x = x := by
    constructor
    · intro hsigma
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
    · intro heq
      exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq heq⟩
  by_cases heq : D.componentCompletedAction n C (1 : G) x = x
  · have hsigma := hsigma_iff.mpr heq
    rw [if_neg (fun hne ↦ hne hsigma), if_neg (fun hne ↦ hne heq)]
  · have hsigma :
        (show D.completedComponentModel n from
          ⟨C, D.componentCompletedAction n C (1 : G) x⟩) ≠
        (show D.completedComponentModel n from ⟨C, x⟩) :=
      fun hs ↦ heq (hsigma_iff.mp hs)
    rw [if_pos hsigma, if_pos heq]

/-- The total completed permutations are asymptotically multiplicative at
the ambient model scale. -/
theorem completedComponentPerm_multiplicationError_negligible
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) (g h : G) :
    Negligible (fun n ↦ (Fintype.card (D.completedComponentModel n) : ℝ))
      (fun n ↦ ((hammingDisagreement
        (D.completedComponentPerm n (g * h))
        (D.completedComponentPerm n g *
          D.completedComponentPerm n h)).card : ℝ)) := by
  have hnegligible :=
    D.componentMultiplicationError_sum_negligible hsymm hgen g h
  unfold Negligible at hnegligible ⊢
  apply Vanishing.congr hnegligible
  intro n
  change ((∑ C : D.componentIndex n,
      ((D.componentMultiplicationError n C g h).card : ℝ)) /
        (Fintype.card (S.model n) : ℝ)) =
    (((hammingDisagreement (D.completedComponentPerm n (g * h))
      (D.completedComponentPerm n g *
        D.completedComponentPerm n h)).card : ℝ) /
      (Fintype.card (D.completedComponentModel n) : ℝ))
  rw [D.card_completedComponentPerm_multiplicationError n g h,
    D.card_completedComponentModel n]
  push_cast
  rfl

/-- The total completed identity permutations have negligible error at the
ambient model scale. -/
theorem completedComponentPerm_identityError_negligible
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (D.completedComponentModel n) : ℝ))
      (fun n ↦ ((hammingDisagreement
        (D.completedComponentPerm n (1 : G)) 1).card : ℝ)) := by
  have hnegligible := D.componentIdentityError_sum_negligible hsymm hgen
  unfold Negligible at hnegligible ⊢
  apply Vanishing.congr hnegligible
  intro n
  change ((∑ C : D.componentIndex n,
      ((D.componentIdentityError n C).card : ℝ)) /
        (Fintype.card (S.model n) : ℝ)) =
    (((hammingDisagreement (D.completedComponentPerm n (1 : G)) 1).card : ℝ) /
      (Fintype.card (D.completedComponentModel n) : ℝ))
  rw [D.card_completedComponentPerm_identityError n,
    D.card_completedComponentModel n]
  push_cast
  rfl

end ExpanderDecomposition
end GroupApproximation
