import GroupApproximation.Kazhdan.KazhdanProjection
import GroupApproximation.Kazhdan.KazhdanFiniteModel

/-!
# Rounding an invariant projection to an invariant finite subset

For an exact finite permutation action, project a characteristic vector onto
the subspace of invariant vectors and threshold the result at `1/2`.  The
resulting finite subset is exactly invariant.  Every membership changed by
the threshold contributes at least `1/4` to the squared distance from the
invariant projection, giving the quantitative bridge from a Kazhdan
projection estimate to a finite symmetric-difference estimate.
-/

namespace GroupApproximation
namespace KazhdanInvariantRounding

open scoped InnerProductSpace symmDiff

universe u v

variable {G : Type u} [Group G]
variable {Y : Type v} [Fintype Y] [DecidableEq Y]

/-- Orthogonal projection of a characteristic vector onto the invariant
subspace of an exact finite permutation action. -/
noncomputable def projectedIndicator (σ : G →* Equiv.Perm Y)
    (U : Finset Y) : EuclideanSpace ℝ Y :=
  KazhdanProjection.invariantProjection
    (KazhdanFiniteModel.permutationRepresentation σ)
    (KazhdanFiniteModel.indicator U)

/-- Threshold the invariant projection at `1/2`. -/
noncomputable def roundedInvariantSet (σ : G →* Equiv.Perm Y)
    (U : Finset Y) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ (1 / 2 : ℝ) ≤ projectedIndicator σ U y

@[simp] theorem mem_roundedInvariantSet (σ : G →* Equiv.Perm Y)
    (U : Finset Y) (y : Y) :
    y ∈ roundedInvariantSet σ U ↔
      (1 / 2 : ℝ) ≤ projectedIndicator σ U y := by
  classical
  simp [roundedInvariantSet]

/-- The projected characteristic vector is globally invariant. -/
theorem projectedIndicator_invariant (σ : G →* Equiv.Perm Y)
    (U : Finset Y) (g : G) :
    KazhdanFiniteModel.permutationRepresentation σ g
        (projectedIndicator σ U) = projectedIndicator σ U := by
  let ρ := KazhdanFiniteModel.permutationRepresentation σ
  let W := KazhdanOrthogonal.invariantSubmodule ρ
  have hp : projectedIndicator σ U ∈ W := by
    change KazhdanProjection.invariantProjection ρ
      (KazhdanFiniteModel.indicator U) ∈ W
    unfold KazhdanProjection.invariantProjection
    exact W.starProjection_apply_mem _
  exact (KazhdanOrthogonal.mem_invariantSubmodule ρ
    (projectedIndicator σ U)).mp hp g

/-- Values of the invariant projection are constant along every action
edge. -/
theorem projectedIndicator_apply_action (σ : G →* Equiv.Perm Y)
    (U : Finset Y) (g : G) (y : Y) :
    projectedIndicator σ U (σ g y) = projectedIndicator σ U y := by
  have h := congrArg (fun z : EuclideanSpace ℝ Y ↦ z (σ g y))
    (projectedIndicator_invariant σ U g)
  simpa only [KazhdanFiniteModel.permutationRepresentation_apply,
    Equiv.symm_apply_apply] using h.symm

/-- The thresholded set is exactly invariant under every group element. -/
theorem roundedInvariantSet_map (σ : G →* Equiv.Perm Y)
    (U : Finset Y) (g : G) :
    (roundedInvariantSet σ U).map (σ g).toEmbedding =
      roundedInvariantSet σ U := by
  classical
  ext y
  simp only [Finset.mem_map, mem_roundedInvariantSet]
  constructor
  · rintro ⟨x, hx, hxy⟩
    subst y
    change (1 / 2 : ℝ) ≤ projectedIndicator σ U (σ g x)
    rw [projectedIndicator_apply_action]
    exact hx
  · intro hy
    refine ⟨σ g⁻¹ y, ?_, ?_⟩
    · rw [projectedIndicator_apply_action]
      exact hy
    · simp

/-- A point whose membership changes after thresholding is at squared
distance at least `1/4` from the invariant projection. -/
theorem quarter_le_sq_indicator_sub_projected_of_mem_symmDiff
    (σ : G →* Equiv.Perm Y) (U : Finset Y) {y : Y}
    (hy : (y ∈ U ∧ y ∉ roundedInvariantSet σ U) ∨
      (y ∈ roundedInvariantSet σ U ∧ y ∉ U)) :
    (1 / 4 : ℝ) ≤
      (KazhdanFiniteModel.indicator U y - projectedIndicator σ U y) ^ 2 := by
  classical
  rw [KazhdanFiniteModel.indicator_apply]
  rcases hy with ⟨hyU, hyV⟩ | ⟨hyV, hyU⟩
  · rw [if_pos hyU]
    have hp : projectedIndicator σ U y < 1 / 2 := by
      simpa only [mem_roundedInvariantSet, not_le] using hyV
    nlinarith [sq_nonneg (projectedIndicator σ U y - 1 / 2)]
  · rw [if_neg hyU]
    have hp : 1 / 2 ≤ projectedIndicator σ U y :=
      (mem_roundedInvariantSet σ U y).mp hyV
    nlinarith [sq_nonneg (projectedIndicator σ U y - 1 / 2)]

/-- Thresholding changes at most four times the squared Hilbert distance to
the invariant projection. -/
theorem card_symmDiff_roundedInvariantSet_le
    (σ : G →* Equiv.Perm Y) (U : Finset Y) :
    (((U ∆ roundedInvariantSet σ U).card : ℕ) : ℝ) ≤
      4 * ‖KazhdanFiniteModel.indicator U - projectedIndicator σ U‖ ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [show (((U ∆ roundedInvariantSet σ U).card : ℕ) : ℝ) =
      ∑ y : Y, if y ∈ U ∆ roundedInvariantSet σ U then (1 : ℝ) else 0 by
        simp]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  change (if y ∈ U ∆ roundedInvariantSet σ U then (1 : ℝ) else 0) ≤
    4 * (KazhdanFiniteModel.indicator U y - projectedIndicator σ U y) ^ 2
  by_cases hy : y ∈ U ∆ roundedInvariantSet σ U
  · rw [if_pos hy]
    have hquarter :=
      quarter_le_sq_indicator_sub_projected_of_mem_symmDiff σ U
        ((Finset.mem_symmDiff).mp hy)
    nlinarith
  · rw [if_neg hy]
    positivity

/-- A Kazhdan pair controls the squared distance from a characteristic
vector to its invariant projection by the total labelled boundary of the
set. -/
theorem kazhdan_mul_projectionError_le_boundary
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (σ : G →* Equiv.Perm Y) (U : Finset Y) :
    ε ^ 2 *
        ‖KazhdanFiniteModel.indicator U - projectedIndicator σ U‖ ^ 2 ≤
      ∑ q ∈ Q,
        (((U.map (σ q).toEmbedding ∆ U).card : ℕ) : ℝ) := by
  let ρ := KazhdanFiniteModel.permutationRepresentation σ
  let W := KazhdanOrthogonal.invariantSubmodule ρ
  let x := KazhdanFiniteModel.indicator U
  let p := projectedIndicator σ U
  let m := x - p
  have hpW : p ∈ W := by
    change KazhdanProjection.invariantProjection ρ x ∈ W
    unfold KazhdanProjection.invariantProjection
    exact W.starProjection_apply_mem _
  have hmW : m ∈ Wᗮ := by
    change x - KazhdanProjection.invariantProjection ρ x ∈ Wᗮ
    unfold KazhdanProjection.invariantProjection
    exact W.sub_starProjection_mem_orthogonal _
  by_cases hm : m = 0
  · calc
      ε ^ 2 * ‖x - p‖ ^ 2 = 0 := by
        rw [show x - p = m by rfl, hm]
        norm_num
      _ ≤ ∑ q ∈ Q,
          (((U.map (σ q).toEmbedding ∆ U).card : ℕ) : ℝ) :=
        Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  · obtain ⟨q, hqQ, hmove⟩ :=
      KazhdanOrthogonal.exists_moved_mul_norm_of_mem_orthogonal
        hQ ρ hmW hm
    have hpfix : ρ q p = p :=
      (KazhdanOrthogonal.mem_invariantSubmodule ρ p).mp hpW q
    have hmoveEq : ρ q m - m = ρ q x - x := by
      change ρ q (x - p) - (x - p) = ρ q x - x
      rw [map_sub, hpfix]
      abel
    have hsq : (ε * ‖m‖) ^ 2 ≤ ‖ρ q m - m‖ ^ 2 := by
      apply (sq_le_sq₀ (mul_nonneg hQ.1.le (norm_nonneg _))
        (norm_nonneg _)).2
      exact hmove
    have hboundary : ‖ρ q x - x‖ ^ 2 =
        (((U.map (σ q).toEmbedding ∆ U).card : ℕ) : ℝ) := by
      change ‖KazhdanFiniteModel.permutationOperator (σ q)
          (KazhdanFiniteModel.indicator U) -
        KazhdanFiniteModel.indicator U‖ ^ 2 = _
      rw [KazhdanFiniteModel.permutationOperator_indicator,
        KazhdanFiniteModel.norm_indicator_sub_sq]
    have hqbound : ε ^ 2 * ‖x - p‖ ^ 2 ≤
        (((U.map (σ q).toEmbedding ∆ U).card : ℕ) : ℝ) := by
      change ε ^ 2 * ‖m‖ ^ 2 ≤ _
      rw [← hboundary, ← hmoveEq]
      nlinarith
    exact hqbound.trans (Finset.single_le_sum
      (f := fun g ↦ (((U.map (σ g).toEmbedding ∆ U).card : ℕ) : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) hqQ)

/-- **Exact finite invariant-relation rounding.**  The thresholded invariant
set differs from the original set by at most `4/ε²` times its total labelled
boundary, stated without division so it remains valid uniformly. -/
theorem kazhdan_mul_card_symmDiff_rounded_le_boundary
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (σ : G →* Equiv.Perm Y) (U : Finset Y) :
    ε ^ 2 * (((U ∆ roundedInvariantSet σ U).card : ℕ) : ℝ) ≤
      4 * ∑ q ∈ Q,
        (((U.map (σ q).toEmbedding ∆ U).card : ℕ) : ℝ) := by
  have hround := card_symmDiff_roundedInvariantSet_le σ U
  have hproj := kazhdan_mul_projectionError_le_boundary hQ σ U
  have hε : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hmul := mul_le_mul_of_nonneg_left hround hε
  nlinarith

end KazhdanInvariantRounding
end GroupApproximation
