import GroupApproximation.Analysis.BoundedCStarSequenceEvaluation
import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.ShulmanCoronaSquareRootAlgebraic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Coordinatewise positive square roots in a C-star product

This is the bounded-sequence input for the quotient-corona proof that
asymptotic commutation is preserved by positive square roots.
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)]

noncomputable local instance naturalityBoundedNontrivial :
    Nontrivial (BoundedCStarSequence A) := by
  let a : A 0 := Classical.choose (exists_ne (0 : A 0))
  have ha : a ≠ 0 := Classical.choose_spec (exists_ne (0 : A 0))
  refine ⟨lp.single ⊤ 0 a, 0, ?_⟩
  intro h
  have h0 := congrArg (fun z : BoundedCStarSequence A ↦ z 0) h
  simp only [lp.single_apply_self] at h0
  exact ha h0

noncomputable local instance naturalityCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance naturalityCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

noncomputable local instance naturalityBoundedPartialOrder :
    PartialOrder (BoundedCStarSequence A) :=
  CStarAlgebra.spectralOrder (BoundedCStarSequence A)

noncomputable local instance naturalityBoundedStarOrderedRing :
    StarOrderedRing (BoundedCStarSequence A) :=
  CStarAlgebra.spectralOrderedRing (BoundedCStarSequence A)

noncomputable local instance naturalityBoundedRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ
      (BoundedCStarSequence A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    (A := BoundedCStarSequence A)

noncomputable local instance naturalityBoundedNonnegSpectrum :
    NonnegSpectrumClass ℝ (BoundedCStarSequence A) :=
  CStarAlgebra.instNonnegSpectrumClass'
    (A := BoundedCStarSequence A)

noncomputable local instance naturalityBoundedNNRealCFC :
    NonUnitalContinuousFunctionalCalculus NNReal
      (BoundedCStarSequence A)
      (fun a : BoundedCStarSequence A ↦ 0 ≤ a) :=
  Nonneg.instNonUnitalContinuousFunctionalCalculus
    (A := BoundedCStarSequence A)

/-- The coordinatewise square-root sequence agrees with continuous functional
calculus in the bounded C-star product. -/
theorem sqrtSequence_eq_cfc_sqrt
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    sqrtSequence A a ha = CFC.sqrt a := by
  have haNonneg : 0 ≤ a := by
    have hrootStar := sqrtSequence_isSelfAdjoint A a ha
    rw [← sqrtSequence_mul_self A a ha]
    nth_rw 1 [← hrootStar.star_eq]
    exact star_mul_self_nonneg (sqrtSequence A a ha)
  apply lp.ext
  funext n
  symm
  exact (boundedCStarSequenceEval A n).map_cfcₙ
    NNReal.sqrt a
    (hφ := continuous_boundedCStarSequenceEval A n)
    (ha := haNonneg)
    (hφa := ha n)

/-- Coordinatewise positivity is the spectral positivity of the bounded
square-root sequence. -/
theorem sqrtSequence_nonneg_bounded
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    0 ≤ sqrtSequence A a ha := by
  rw [sqrtSequence_eq_cfc_sqrt A a ha]
  exact CFC.sqrt_nonneg a

end

end ShulmanCoronaSquareRoot
end GroupApproximation
