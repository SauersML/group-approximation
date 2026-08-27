import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Coordinatewise contractive representatives in a norm-matrix corona

Every contraction in a norm-matrix corona has a representative which is a
contraction in every coordinate.  Starting with an arbitrary representative,
we divide its `n`th coordinate by `max 1 ‖a n‖`.  The corona norm bound implies
that these scalars converge to one, so this normalization does not change the
corona class.
-/

namespace GroupApproximation
namespace ShulmanCoronaContractionRepresentative

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable (X : ℕ → Type u) [∀ n, Fintype (X n)]
  [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]

/-- The linear map whose value at `1` is a prescribed bounded sequence. -/
def scalarLift (a : BoundedMatrixSequence X) :
    ℂ →ₗ[ℂ] BoundedMatrixSequence X where
  toFun c := c • a
  map_add' c d := add_smul c d a
  map_smul' c d := by
    have hcd : c • d = c * d := by rfl
    rw [hcd, RingHom.id_apply, smul_smul]

@[simp] theorem scalarLift_apply
    (a : BoundedMatrixSequence X) (c : ℂ) :
    scalarLift X a c = c • a :=
  rfl

@[simp] theorem scalarLift_one
    (a : BoundedMatrixSequence X) :
    scalarLift X a 1 = a := by
  simp

/-- Coordinatewise normalization of a bounded representative. -/
def normalizeRepresentative
    (a : BoundedMatrixSequence X) :
    BoundedMatrixSequence X :=
  BlackadarKirchberg.normalizeMatrixLift X (scalarLift X a) 1

@[simp] theorem normalizeRepresentative_apply
    (a : BoundedMatrixSequence X) (n : ℕ) :
    normalizeRepresentative X a n =
      ((↑((max (1 : ℝ) ‖a n‖)⁻¹)) : ℂ) • a n := by
  simp [normalizeRepresentative, BlackadarKirchberg.normalizeMatrixLift,
    BlackadarKirchberg.unitNormalizationScale]

/-- Every coordinate of the normalized representative is a contraction. -/
theorem normalizeRepresentative_norm_le_one
    (a : BoundedMatrixSequence X) (n : ℕ) :
    ‖normalizeRepresentative X a n‖ ≤ 1 := by
  rw [normalizeRepresentative_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ max 1 ‖a n‖))]
  have hpos : 0 < max 1 ‖a n‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  calc
    (max 1 ‖a n‖)⁻¹ * ‖a n‖ ≤
        (max 1 ‖a n‖)⁻¹ * max 1 ‖a n‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- Coordinate normalization does not change a corona class whose norm is at
most one. -/
theorem normalizeRepresentative_quotient_eq
    (a : BoundedMatrixSequence X)
    (ha : ‖normMatrixCStarCoronaMk X a‖ ≤ 1) :
    normMatrixCStarCoronaMk X (normalizeRepresentative X a) =
      normMatrixCStarCoronaMk X a := by
  have hmax :=
    BlackadarKirchberg.tendsto_max_one_coord_norm_of_corona_norm_le_one X a ha
  have hs : Tendsto (fun n ↦ (max (1 : ℝ) ‖a n‖)⁻¹) atTop (nhds 1) := by
    simpa only [inv_one] using hmax.inv₀ one_ne_zero
  have hsC : Tendsto (fun n ↦ ((↑((max (1 : ℝ) ‖a n‖)⁻¹)) : ℂ))
      atTop (nhds 1) := (Complex.continuous_ofReal.tendsto 1).comp hs
  have hscalar : Tendsto
      (fun n ↦ ‖((↑((max (1 : ℝ) ‖a n‖)⁻¹)) : ℂ) - 1‖)
      atTop (nhds 0) := by
    have hsub := hsC.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1))
    have hnorm := hsub.norm
    simpa only [sub_self, norm_zero] using hnorm
  have hnull : IsNullMatrixSequence X cofinite
      (normalizeRepresentative X a - a) := by
    rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop]
    refine squeeze_zero'
      (g := fun n ↦
        ‖((↑((max (1 : ℝ) ‖a n‖)⁻¹)) : ℂ) - 1‖ * ‖a‖)
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun n ↦ by
        have hcoord : (normalizeRepresentative X a - a) n =
            (((↑((max (1 : ℝ) ‖a n‖)⁻¹)) : ℂ) - 1) • a n := by
          rw [lp.coeFn_sub, Pi.sub_apply, normalizeRepresentative_apply,
            sub_smul, one_smul]
        rw [hcoord, norm_smul]
        exact mul_le_mul_of_nonneg_left
          (boundedMatrixSequence_coord_norm_le X a n) (norm_nonneg _)
    · simpa only [zero_mul, mul_comm] using hscalar.const_mul ‖a‖
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  exact hnull

/-- Every contraction in the quotient has a representative which is
contractive in every coordinate. -/
theorem exists_coordinatewise_contractive_representative
    (q : NormMatrixCStarCorona X) (hq : ‖q‖ ≤ 1) :
    ∃ a : BoundedMatrixSequence X,
      (∀ n, ‖a n‖ ≤ 1) ∧
        normMatrixCStarCoronaMk X a = q := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective X q
  refine ⟨normalizeRepresentative X a,
    normalizeRepresentative_norm_le_one X a,
    normalizeRepresentative_quotient_eq X a hq⟩

/-- Closed endpoint for coordinatewise contractive representative selection. -/
def CoordinatewiseContractiveRepresentative : Prop :=
  ∀ (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (q : NormMatrixCStarCorona X), ‖q‖ ≤ 1 →
      ∃ a : BoundedMatrixSequence X,
        (∀ n, ‖a n‖ ≤ 1) ∧
          normMatrixCStarCoronaMk X a = q

/-- Coordinatewise contractive representatives exist for all contractions in
all norm-matrix coronas. -/
theorem coordinatewiseContractiveRepresentative :
    CoordinatewiseContractiveRepresentative := by
  intro X _ _ _ q hq
  exact exists_coordinatewise_contractive_representative X q hq

end


end ShulmanCoronaContractionRepresentative
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanCoronaContractionRepresentative.coordinatewiseContractiveRepresentative
