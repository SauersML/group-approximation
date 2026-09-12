import GroupApproximation.Analysis.CStarStinespringAct
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The defect square root, and the unconditional dilation bound

## What this module proves

`CStarStinespringAct` bounds the dilation action by `‖c‖` *given* an
exhibition of the defect `‖c‖² • 1 - star c * c` as `star d * d`.  This
module supplies the exhibition: the defect is nonnegative because
`star c * c` is dominated by its norm, and a nonnegative element of a
C⋆-algebra is a `star d * d`.

The exported statements are order-free.  As in `CStarStateGNS`, the
canonical spectral order (`CStarAlgebra.spectralOrder`) is installed as
a *local* instance, specialised to the variable `A`, and every exported
declaration bakes it into its term: consumers see only the algebra.

* `exists_defect_sqrt` -- the exhibition;
* `norm_stinespringActPre_le_norm` -- the unconditional seminorm bound
  `‖π(c) f‖ ≤ ‖c‖ ‖f‖` on the dilation pre-space.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

universe u w

variable {A : Type u} [CStarAlgebra A]

section SpectralBridge

noncomputable local instance (priority := 0) instDefectSpectralOrder :
    PartialOrder A :=
  CStarAlgebra.spectralOrder A

noncomputable local instance (priority := 0) instDefectSpectralStarOrdered :
    StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- **The defect square root**: `‖c‖² • 1 - star c * c` is a
`star d * d`.  The statement mentions no order; the spectral order is
local to the proof. -/
theorem exists_defect_sqrt (c : A) :
    ∃ d : A, star d * d = ((‖c‖ ^ 2 : ℝ) : ℂ) • (1 : A) - star c * c := by
  have h1 : star c * c ≤ algebraMap ℝ A ‖star c * c‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.star_mul_self c)
  have h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) • (1 : A)
      = algebraMap ℝ A ‖star c * c‖ := by
    rw [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_algebraMap, algebraMap_smul, pow_two]
  have h3 : (0 : A) ≤ ((‖c‖ ^ 2 : ℝ) : ℂ) • (1 : A) - star c * c := by
    rw [h2]
    exact sub_nonneg.mpr h1
  obtain ⟨d, hd⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h3
  exact ⟨d, hd.symm⟩

end SpectralBridge

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (φ : A →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositive φ)

/-- **The unconditional dilation bound**: multiplication by `c` on the
dilation pre-space is bounded by `‖c‖`. -/
theorem norm_stinespringActPre_le_norm (c : A)
    (f : StinespringPre φ hφ) :
    ‖stinespringActPre φ hφ c f‖ ≤ ‖c‖ * ‖f‖ := by
  obtain ⟨d, hd⟩ := exists_defect_sqrt c
  exact norm_stinespringActPre_le φ hφ c d hd f

end CStarExactness
end GroupApproximation
