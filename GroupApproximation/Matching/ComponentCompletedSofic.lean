import GroupApproximation.Matching.ComponentCompletedAction

/-!
# The completed component labels form a sofic approximation

The componentwise completions may be transported back to the original
finite model.  Their total multiplication defect is negligible, and their
total disagreement with the original sofic approximation is negligible for
every fixed group element.  Consequently the transported completions retain
asymptotic faithfulness and give a second, block-preserving sofic
approximation of the whole group.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- Conjugating two permutations across an equivalence preserves their
Hamming-disagreement count. -/
theorem card_hammingDisagreement_permCongr
    {Y Z : FiniteModel} (e : Y ≃ Z) (p q : Equiv.Perm Y) :
    (hammingDisagreement (e.permCongr p) (e.permCongr q)).card =
      (hammingDisagreement p q).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ ↦ e x)
  · intro x hx
    simp only [mem_hammingDisagreement] at hx ⊢
    simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using
      e.injective.ne hx
  · intro x _ y _ hxy
    exact e.injective hxy
  · intro z hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simp only [mem_hammingDisagreement] at hz ⊢
    intro hpq
    apply hz
    simpa only [Equiv.permCongr_apply, e.apply_symm_apply] using
      congrArg e hpq

/-- Hamming distance itself is invariant under transport across a finite
equivalence. -/
theorem hammingDistance_permCongr
    {Y Z : FiniteModel} (e : Y ≃ Z) (p q : Equiv.Perm Y) :
    hammingDistance Z (e.permCongr p) (e.permCongr q) =
      hammingDistance Y p q := by
  unfold hammingDistance
  rw [card_hammingDisagreement_permCongr e p q,
    Fintype.card_congr e]

/-- Transport of permutations respects their group multiplication. -/
theorem permCongr_mul {Y Z : Type} (e : Y ≃ Z)
    (p q : Equiv.Perm Y) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q := by
  ext x
  simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply,
    e.symm_apply_apply]

/-- The blockwise completed permutations, transported to the original
finite model. -/
noncomputable def completedAmbientPerm (n : ℕ) (g : G) :
    Equiv.Perm (S.model n) :=
  (D.completedComponentEquiv n).permCongr (D.completedComponentPerm n g)

/-- The ambient permutation, transported to the component disjoint union. -/
noncomputable def ambientComponentPerm (n : ℕ) (g : G) :
    Equiv.Perm (D.completedComponentModel n) :=
  (D.completedComponentEquiv n).symm.permCongr (S.map n g)

/-- On the tagged component model, disagreement with the transported ambient
action is exactly the sum of the componentwise disagreement sets. -/
theorem completedComponentPerm_ambient_disagreement_card (n : ℕ) (g : G) :
    ((hammingDisagreement (D.completedComponentPerm n g)
      (D.ambientComponentPerm n g)).card : ℝ) =
      ∑ C : D.componentIndex n,
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          (D.componentCompletedAction n C g x : S.model n) ≠
            S.map n g (x : S.model n)).card : ℝ) := by
  classical
  unfold hammingDisagreement
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  change (∑ a : (Σ C : D.componentIndex n,
      indexedBlockModel (D.blocks n) C),
        if D.completedComponentPerm n g a ≠ D.ambientComponentPerm n g a
        then 1 else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  have hperm_iff :
      D.completedComponentPerm n g
          (show D.completedComponentModel n from ⟨C, x⟩) =
        D.ambientComponentPerm n g
          (show D.completedComponentModel n from ⟨C, x⟩) ↔
      (D.componentCompletedAction n C g x : S.model n) =
        S.map n g (x : S.model n) := by
    constructor
    · intro heq
      have h := congrArg (D.completedComponentEquiv n) heq
      simpa only [completedComponentPerm_apply, ambientComponentPerm,
        Equiv.permCongr_apply, completedComponentEquiv_apply,
        Equiv.apply_symm_apply, Equiv.symm_symm] using h
    · intro heq
      apply (D.completedComponentEquiv n).injective
      simpa only [completedComponentPerm_apply, ambientComponentPerm,
        Equiv.permCongr_apply, completedComponentEquiv_apply,
        Equiv.apply_symm_apply, Equiv.symm_symm] using heq
  by_cases heq : (D.componentCompletedAction n C g x : S.model n) =
      S.map n g (x : S.model n)
  · have hp := hperm_iff.mpr heq
    rw [if_neg (fun hne ↦ hne hp), if_neg (fun hne ↦ hne heq)]
  · have hp : D.completedComponentPerm n g
        (show D.completedComponentModel n from ⟨C, x⟩) ≠
      D.ambientComponentPerm n g
        (show D.completedComponentModel n from ⟨C, x⟩) :=
      fun h ↦ heq (hperm_iff.mp h)
    rw [if_pos hp, if_pos heq]

/-- Transported completion disagreement is negligible for every fixed group
element. -/
theorem completedAmbientPerm_disagreement_negligible
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) (g : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ((hammingDisagreement
        (D.completedAmbientPerm n g) (S.map n g)).card : ℝ)) := by
  have hcomponent := Negligible.congr
    (D.componentCompletedAction_disagreement_sum_negligible hsymm hgen g)
    (fun n ↦ (D.completedComponentPerm_ambient_disagreement_card n g).symm)
  apply Negligible.congr hcomponent
  intro n
  norm_cast
  unfold completedAmbientPerm ambientComponentPerm
  rw [← card_hammingDisagreement_permCongr (D.completedComponentEquiv n)
    (D.completedComponentPerm n g)
    ((D.completedComponentEquiv n).symm.permCongr (S.map n g))]
  have htransport :
      (D.completedComponentEquiv n).permCongr
          ((D.completedComponentEquiv n).symm.permCongr (S.map n g)) =
        S.map n g := by
    ext y
    simp only [Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  rw [htransport]

/-- The transported component completions give a genuine sofic
approximation.  This packages the completed labels in exactly the form
consumed by the Kazhdan and centralizer arguments. -/
noncomputable def completedSoficApproximation
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) : SoficApproximation G where
  model := S.model
  map := D.completedAmbientPerm
  card_tendsToInfinity := S.card_tendsToInfinity
  asymptoticallyMultiplicative := by
    intro g h ε hε
    have hnegligible :=
      D.completedComponentPerm_multiplicationError_negligible hsymm hgen g h
    unfold Negligible Vanishing at hnegligible
    obtain ⟨N, hN⟩ := hnegligible ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    change hammingDistance (S.model n)
      ((D.completedComponentEquiv n).permCongr
        (D.completedComponentPerm n (g * h)))
      ((D.completedComponentEquiv n).permCongr
          (D.completedComponentPerm n g) *
        (D.completedComponentEquiv n).permCongr
          (D.completedComponentPerm n h)) < ε
    rw [← permCongr_mul]
    rw [hammingDistance_permCongr]
    have h := hN n hn
    unfold hammingDistance at h ⊢
    rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))] at h
    exact h
  asymptoticallyFaithful := by
    intro g hg ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨N₁, hN₁⟩ := S.asymptoticallyFaithful g hg (ε / 2) hhalf
    have hcloseNeg :=
      D.completedAmbientPerm_disagreement_negligible hsymm hgen g
    unfold Negligible Vanishing at hcloseNeg
    obtain ⟨N₂, hN₂⟩ := hcloseNeg (ε / 2) hhalf
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    have hfaith := hN₁ n ((le_max_left N₁ N₂).trans hn)
    have hclose := hN₂ n ((le_max_right N₁ N₂).trans hn)
    have hclose' : hammingDistance (S.model n)
        (D.completedAmbientPerm n g) (S.map n g) < ε / 2 := by
      unfold hammingDistance
      rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))] at hclose
      exact hclose
    have htriangle := hammingDistance_triangle (S.model n)
      (S.map n g) (D.completedAmbientPerm n g) 1
    rw [hammingDistance_comm (S.model n) (S.map n g)
      (D.completedAmbientPerm n g)] at htriangle
    linarith

/-- The same completed approximation on its native tagged disjoint union.
Unlike the transported version, this presentation exposes exact component
preservation definitionally. -/
noncomputable def completedComponentSoficApproximation
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) : SoficApproximation G where
  model := D.completedComponentModel
  map := D.completedComponentPerm
  card_tendsToInfinity := by
    intro M
    obtain ⟨N, hN⟩ := S.card_tendsToInfinity M
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [D.card_completedComponentModel n]
    exact hN n hn
  asymptoticallyMultiplicative := by
    intro g h ε hε
    have hnegligible :=
      D.completedComponentPerm_multiplicationError_negligible hsymm hgen g h
    unfold Negligible Vanishing at hnegligible
    obtain ⟨N, hN⟩ := hnegligible ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h := hN n hn
    unfold hammingDistance at h ⊢
    rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))] at h
    exact h
  asymptoticallyFaithful := by
    intro g hg ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨N₁, hN₁⟩ := S.asymptoticallyFaithful g hg (ε / 2) hhalf
    have hcloseNeg := Negligible.congr
      (D.componentCompletedAction_disagreement_sum_negligible hsymm hgen g)
      (fun n ↦ (D.completedComponentPerm_ambient_disagreement_card n g).symm)
    unfold Negligible Vanishing at hcloseNeg
    obtain ⟨N₂, hN₂⟩ := hcloseNeg (ε / 2) hhalf
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    have hfaith := hN₁ n ((le_max_left N₁ N₂).trans hn)
    have hclose := hN₂ n ((le_max_right N₁ N₂).trans hn)
    have hambfaith : 1 - ε / 2 < hammingDistance
        (D.completedComponentModel n) (D.ambientComponentPerm n g) 1 := by
      have htransport := hammingDistance_permCongr
        (D.completedComponentEquiv n).symm (S.map n g) 1
      rw [← htransport] at hfaith
      have hone : (D.completedComponentEquiv n).symm.permCongr
          (1 : Equiv.Perm (S.model n)) = 1 := by
        ext y
        simp only [Equiv.permCongr_apply, Equiv.Perm.one_apply,
          Equiv.apply_symm_apply]
      rw [hone] at hfaith
      exact hfaith
    have hclose' : hammingDistance (D.completedComponentModel n)
        (D.completedComponentPerm n g) (D.ambientComponentPerm n g) < ε / 2 := by
      unfold hammingDistance
      rw [D.card_completedComponentModel n]
      rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))] at hclose
      exact hclose
    have htriangle := hammingDistance_triangle (D.completedComponentModel n)
      (D.ambientComponentPerm n g) (D.completedComponentPerm n g) 1
    rw [hammingDistance_comm (D.completedComponentModel n)
      (D.ambientComponentPerm n g) (D.completedComponentPerm n g)] at htriangle
    linarith

/-- Every completed group label preserves its component tag exactly. -/
@[simp] theorem completedComponentPerm_fst (n : ℕ) (g : G)
    (x : D.completedComponentModel n) :
    (D.completedComponentPerm n g x).1 = x.1 := rfl

end ExpanderDecomposition
end GroupApproximation
