import GroupApproximation.Analysis.LanceCPApprox
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Unit-defect control for completely positive contractions

The completely positive approximation property in `CStarExactness` supplies
contractive maps, whereas the Lance route consumes unital maps.  The standard
unitalization starts from the positive defects

```text
  1 - alpha(1),       1 - beta(1).
```

This file proves that positivity and the quantitative estimate which makes the
repair usable.  If `beta (alpha 1)` is within `delta` of `1`, then both the
outgoing defect `1 - beta 1` and the image `beta (1 - alpha 1)` of the incoming
defect have norm at most `delta`.

No finite-dimensional structure is used here.  The remaining step is to add
state-valued rank-one completely positive corrections and then transport the
finite-dimensional algebra through its Wedderburn decomposition.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v w

noncomputable section

/-- The unit defect of a completely positive contraction is positive. -/
theorem one_sub_map_one_nonneg_of_completelyPositive_contractive
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B]
    (phi : A →ₗ[ℂ] B) (hphi : IsCompletelyPositive phi)
    (hcontract : ∀ a : A, ‖phi a‖ ≤ ‖a‖) :
    0 ≤ (1 : B) - phi 1 := by
  have hpos : 0 ≤ phi (1 : A) :=
    map_nonneg_of_completelyPositive hphi (show 0 ≤ (1 : A) from zero_le_one)
  have hnorm : ‖phi (1 : A)‖ ≤ 1 := by
    have honeSq : ‖(1 : A)‖ = ‖(1 : A)‖ ^ 2 := by
      have honeCstar : ‖star (1 : A) * (1 : A)‖ =
          ‖(1 : A)‖ * ‖(1 : A)‖ := CStarRing.norm_star_mul_self
      simpa [sq] using honeCstar
    have honeLe : ‖(1 : A)‖ ≤ 1 := by
      nlinarith [norm_nonneg (1 : A)]
    calc
      ‖phi (1 : A)‖ ≤ ‖(1 : A)‖ := hcontract (1 : A)
      _ ≤ 1 := honeLe
  exact sub_nonneg.mpr
    ((CStarAlgebra.norm_le_one_iff_of_nonneg (phi (1 : A)) hpos).mp hnorm)

/-- Approximation at the unit controls the outgoing unit defect. -/
theorem norm_one_sub_second_one_le_of_cp_contractions
    {A : Type u} {D : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra B]
    (alpha : A →ₗ[ℂ] D) (beta : D →ₗ[ℂ] B)
    (halpha : IsCompletelyPositive alpha)
    (hbeta : IsCompletelyPositive beta)
    (halphaContract : ∀ a : A, ‖alpha a‖ ≤ ‖a‖)
    (hbetaContract : ∀ d : D, ‖beta d‖ ≤ ‖d‖)
    {delta : ℝ} (hunit : ‖beta (alpha 1) - 1‖ ≤ delta) :
    ‖1 - beta 1‖ ≤ delta := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hAlphaDefect : 0 ≤ (1 : D) - alpha 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      alpha halpha halphaContract
  have hBetaDefect : 0 ≤ (1 : B) - beta 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      beta hbeta hbetaContract
  have hImageDefect : 0 ≤ beta ((1 : D) - alpha 1) :=
    map_nonneg_of_completelyPositive hbeta hAlphaDefect
  have hsplit : beta ((1 : D) - alpha 1) = beta 1 - beta (alpha 1) := by
    rw [map_sub]
  have hle : (1 : B) - beta 1 ≤ 1 - beta (alpha 1) := by
    rw [sub_le_sub_iff_left]
    rw [← sub_nonneg, ← hsplit]
    exact hImageDefect
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hBetaDefect hle
  calc
    ‖1 - beta 1‖ ≤ ‖1 - beta (alpha 1)‖ := hnorm
    _ = ‖beta (alpha 1) - 1‖ := by rw [← norm_neg, neg_sub]
    _ ≤ delta := hunit

/-- Approximation at the unit controls the image of the incoming unit defect. -/
theorem norm_second_incoming_unit_defect_le_of_cp_contractions
    {A : Type u} {D : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra B]
    (alpha : A →ₗ[ℂ] D) (beta : D →ₗ[ℂ] B)
    (halpha : IsCompletelyPositive alpha)
    (hbeta : IsCompletelyPositive beta)
    (halphaContract : ∀ a : A, ‖alpha a‖ ≤ ‖a‖)
    (hbetaContract : ∀ d : D, ‖beta d‖ ≤ ‖d‖)
    {delta : ℝ} (hunit : ‖beta (alpha 1) - 1‖ ≤ delta) :
    ‖beta ((1 : D) - alpha 1)‖ ≤ delta := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hAlphaDefect : 0 ≤ (1 : D) - alpha 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      alpha halpha halphaContract
  have hImageDefect : 0 ≤ beta ((1 : D) - alpha 1) :=
    map_nonneg_of_completelyPositive hbeta hAlphaDefect
  have hBetaDefect : 0 ≤ (1 : B) - beta 1 :=
    one_sub_map_one_nonneg_of_completelyPositive_contractive
      beta hbeta hbetaContract
  have hsplit : beta ((1 : D) - alpha 1) = beta 1 - beta (alpha 1) := by
    rw [map_sub]
  have hle : beta ((1 : D) - alpha 1) ≤ 1 - beta (alpha 1) := by
    rw [hsplit]
    exact sub_le_sub_right (sub_nonneg.mp hBetaDefect) _
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hImageDefect hle
  calc
    ‖beta ((1 : D) - alpha 1)‖ ≤ ‖1 - beta (alpha 1)‖ := hnorm
    _ = ‖beta (alpha 1) - 1‖ := by rw [← norm_neg, neg_sub]
    _ ≤ delta := hunit

end

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

#audit_axioms one_sub_map_one_nonneg_of_completelyPositive_contractive
#audit_axioms norm_one_sub_second_one_le_of_cp_contractions
#audit_axioms norm_second_incoming_unit_defect_le_of_cp_contractions
