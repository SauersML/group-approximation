import GroupApproximation.Analysis.ShulmanCoronaContractionRepresentative
import GroupApproximation.Meta.AxiomGuard

/-!
# Representatives with a prescribed coordinate norm bound

The coordinatewise contraction selection theorem rescales to every
nonnegative radius.  This is the representative-selection form used when a
contractive asymptotic lift is assembled element by element.
-/

namespace GroupApproximation
namespace ShulmanCoronaBoundedRepresentative

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable (X : ℕ → Type u) [∀ n, Fintype (X n)]
  [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]

/-- A corona element of norm at most `r` has a representative whose every
coordinate has norm at most `r`. -/
theorem exists_coordinatewise_bounded_representative
    (q : NormMatrixCStarCorona X) (r : ℝ) (hr : 0 ≤ r) (hq : ‖q‖ ≤ r) :
    ∃ a : BoundedMatrixSequence X,
      (∀ n, ‖a n‖ ≤ r) ∧ normMatrixCStarCoronaMk X a = q := by
  rcases hr.eq_or_lt with rfl | hrpos
  · have hq0 : q = 0 := norm_eq_zero.mp (le_antisymm hq (norm_nonneg q))
    refine ⟨0, ?_, ?_⟩
    · intro n
      simp
    · simp [hq0]
  · let z : ℂ := ((r⁻¹ : ℝ) : ℂ)
    have hz : ‖z‖ = r⁻¹ := by
      rw [show z = ((r⁻¹ : ℝ) : ℂ) by rfl, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr hrpos.le)]
    have hscaled : ‖z • q‖ ≤ 1 := by
      calc
        ‖z • q‖ ≤ ‖z‖ * ‖q‖ := norm_smul_le z q
        _ = r⁻¹ * ‖q‖ := by rw [hz]
        _ ≤ r⁻¹ * r :=
          mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hrpos.le)
        _ = 1 := inv_mul_cancel₀ hrpos.ne'
    obtain ⟨b, hb, hbq⟩ :=
      ShulmanCoronaContractionRepresentative.exists_coordinatewise_contractive_representative
        X (z • q) hscaled
    refine ⟨((r : ℂ) • b), ?_, ?_⟩
    · intro n
      rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg hrpos.le]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hb n) hrpos.le
    · calc
        normMatrixCStarCoronaMk X ((r : ℂ) • b) =
            (r : ℂ) • normMatrixCStarCoronaMk X b :=
          map_smul (normMatrixCStarCoronaQuotient X) (r : ℂ) b
        _ = (r : ℂ) • (z • q) := by rw [hbq]
        _ = ((r : ℂ) * z) • q := smul_smul (r : ℂ) z q
        _ = q := by
          have hrz : (r : ℂ) * z = 1 := by
            rw [show z = ((r⁻¹ : ℝ) : ℂ) by rfl]
            exact_mod_cast (mul_inv_cancel₀ hrpos.ne' : r * r⁻¹ = 1)
          rw [hrz]
          exact one_smul ℂ q

/-- Closed universal form of bounded representative selection. -/
def CoordinatewiseBoundedRepresentative : Prop :=
  ∀ (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (q : NormMatrixCStarCorona X) (r : ℝ), 0 ≤ r → ‖q‖ ≤ r →
      ∃ a : BoundedMatrixSequence X,
        (∀ n, ‖a n‖ ≤ r) ∧ normMatrixCStarCoronaMk X a = q

/-- Every norm bound in the corona lifts to the same bound in every matrix
coordinate. -/
theorem coordinatewiseBoundedRepresentative :
    CoordinatewiseBoundedRepresentative := by
  intro X _ _ _ q r hr hq
  exact exists_coordinatewise_bounded_representative X q r hr hq

end

end ShulmanCoronaBoundedRepresentative
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanCoronaBoundedRepresentative.coordinatewiseBoundedRepresentative
