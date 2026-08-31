import GroupApproximation.Analysis.CStarContinuousMapFiniteInterpolation
import GroupApproximation.Analysis.CStarNuclearProduct
import Mathlib.Topology.PartitionOfUnity

/-!
# Nuclearity of compact continuous-map algebras with finite-dimensional fibre

This is a direct completely-positive approximation proof.  On a prescribed
finite set of continuous functions, compactness supplies finitely many sample
points on which every function varies by less than the tolerance.  A
subordinate continuous partition of unity interpolates those evaluations.
-/

namespace GroupApproximation
namespace CStarContinuousMapFiniteInterpolation

open Set Filter Topology CStarExactness

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [Nonempty X]
variable {B : Type} [CStarAlgebra B] [FiniteDimensional ℂ B]

/-- The common variation neighborhood of a finite family at a point. -/
def variationNeighborhood (F : Finset C(X, B)) (eps : ℝ) (x : X) : Set X :=
  ⋂ f ∈ F, {y | ‖f x - f y‖ < eps}

theorem isOpen_variationNeighborhood (F : Finset C(X, B)) (eps : ℝ) (x : X) :
    IsOpen (variationNeighborhood F eps x) := by
  apply isOpen_biInter_finset
  intro f hf
  exact isOpen_lt (continuous_const.sub f.continuous).norm continuous_const

theorem mem_variationNeighborhood_self (F : Finset C(X, B)) {eps : ℝ}
    (heps : 0 < eps) (x : X) : x ∈ variationNeighborhood F eps x := by
  simp [variationNeighborhood, heps]

/-- A compact space admits finitely many sample points whose common variation
neighborhoods cover the space. -/
theorem exists_finite_variation_cover (F : Finset C(X, B)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ S : Finset X, Set.univ ⊆ ⋃ x ∈ S, variationNeighborhood F eps x := by
  apply isCompact_univ.elim_finite_subcover (variationNeighborhood F eps)
  · exact isOpen_variationNeighborhood F eps
  · intro x _
    exact Set.mem_iUnion.2 ⟨x, mem_variationNeighborhood_self F heps x⟩

/-- The selected sample point corresponding to an enumeration of a finite
subcover. -/
def coverSample (S : Finset X) (i : Fin S.card) : X :=
  (S.equivFin.symm i).1

theorem finite_cover_reindexed (F : Finset C(X, B)) (eps : ℝ)
    (S : Finset X) (hS : Set.univ ⊆ ⋃ x ∈ S, variationNeighborhood F eps x) :
    Set.univ ⊆ ⋃ i : Fin S.card,
      variationNeighborhood F eps (coverSample S i) := by
  intro y _
  obtain ⟨x, hxS, hy⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ y))
  let i : Fin S.card := S.equivFin ⟨x, hxS⟩
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  have hi : S.equivFin.symm i = ⟨x, hxS⟩ :=
    S.equivFin.symm_apply_apply ⟨x, hxS⟩
  simpa [coverSample, i, hi] using hy

/-- Partition-of-unity data subordinate to a finite variation cover. -/
theorem exists_variation_partition (F : Finset C(X, B)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ (k : ℕ) (sample : Fin k → X) (w : Fin k → C(X, ℝ)),
      (∀ i, tsupport (w i) ⊆ variationNeighborhood F eps (sample i)) ∧
      (∀ y, ∑ i, w i y = 1) ∧
      (∀ i y, 0 ≤ w i y) := by
  obtain ⟨S, hS⟩ := exists_finite_variation_cover (B := B) F heps
  let sample : Fin S.card → X := coverSample S
  let U : Fin S.card → Set X := fun i ↦ variationNeighborhood F eps (sample i)
  have hUopen : ∀ i, IsOpen (U i) := fun i ↦
    isOpen_variationNeighborhood F eps (sample i)
  have hUcover : Set.univ ⊆ ⋃ i, U i := by
    simpa only [U, sample] using finite_cover_reindexed F eps S hS
  obtain ⟨w, hwsub, hwsum, hw, _⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hUopen isCompact_univ hUcover
  refine ⟨S.card, sample, w, ?_, ?_, ?_⟩
  · exact hwsub
  · intro y
    simpa only [Finset.sum_apply, Pi.one_apply] using hwsum (Set.mem_univ y)
  · intro i y
    exact (hw i y).1

/-- The interpolation approximation is point-norm close on the chosen finite
set. -/
theorem norm_interpolation_evaluation_sub_le
    (F : Finset C(X, B)) {eps : ℝ} (heps : 0 < eps)
    {k : ℕ} (sample : Fin k → X) (w : Fin k → C(X, ℝ))
    (hwsub : ∀ i, tsupport (w i) ⊆ variationNeighborhood F eps (sample i))
    (hwsum : ∀ y, ∑ i, w i y = 1) (hw : ∀ i y, 0 ≤ w i y)
    (f : C(X, B)) (hf : f ∈ F) :
    ‖finiteInterpolation (B := B) w (finiteEvaluationStarAlgHom sample f) - f‖ ≤ eps := by
  apply (ContinuousMap.norm_le _ heps.le).2
  intro y
  rw [ContinuousMap.sub_apply, finiteInterpolation_apply w hw]
  have hfy : f y = ∑ i, (w i y : ℂ) • f y := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hwsum y,
      Complex.ofReal_one, one_smul]
  rw [hfy, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i, ((w i y : ℂ) • f (sample i) - (w i y : ℂ) • f y)‖
        ≤ ∑ i, ‖(w i y : ℂ) • f (sample i) -
          (w i y : ℂ) • f y‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i y * eps := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw i y)]
      by_cases hwi : w i y = 0
      · simp [hwi]
      · have hysupport : y ∈ Function.support (w i) := by
          simpa [Function.mem_support] using hwi
        have hyvariation := hwsub i (subset_closure hysupport)
        have hclose : ‖f (sample i) - f y‖ ≤ eps := by
          exact le_of_lt ((Set.mem_iInter.1
            (Set.mem_iInter.1 hyvariation f)) hf)
        exact mul_le_mul_of_nonneg_left hclose (hw i y)
    _ = eps := by rw [← Finset.sum_mul, hwsum y, one_mul]

/-- Continuous functions from a compact Hausdorff space into a
finite-dimensional C-star algebra are nuclear, by the explicit finite
evaluation/partition-of-unity CPAP. -/
theorem isNuclearCStarAlgebra_continuousMap :
    IsNuclearCStarAlgebra C(X, B) := by
  intro F eps heps
  obtain ⟨k, sample, w, hwsub, hwsum, hw⟩ :=
    exists_variation_partition (B := B) F heps
  let D : FinDimCStarAlgebra := { carrier := ∀ i : Fin k, B }
  let down : C(X, B) →ₗ[ℂ] D := (finiteEvaluationStarAlgHom sample).toLinearMap
  let up : D →ₗ[ℂ] C(X, B) := finiteInterpolation w
  refine ⟨D, down, up, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [down, D]
    exact isCompletelyPositive_of_starAlgHom
      (finiteEvaluationStarAlgHom (B := B) sample).toNonUnitalStarAlgHom
  · exact isCompletelyPositive_finiteInterpolation w
  · exact norm_finiteEvaluationStarAlgHom_le sample
  · exact norm_finiteInterpolation_le w hw hwsum
  · intro f hf
    exact norm_interpolation_evaluation_sub_le F heps sample w hwsub hwsum hw f hf

end

end CStarContinuousMapFiniteInterpolation
end GroupApproximation
