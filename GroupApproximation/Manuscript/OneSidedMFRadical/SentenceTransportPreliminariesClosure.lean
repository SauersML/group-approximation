import GroupApproximation.Analysis.CoronaProjectionOrder
import GroupApproximation.Analysis.PolarLiftingPrintedSequence
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRemarks
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness

/-!
# Remaining sentence closure before the transport theorem

Row-numbered wrappers for the mathematical claims among census rows 102--125
which were not already named by another `Sentence*Closure` module.  Rows
108--109, 111, 116, 122, and 124 already have exact sentence declarations and
are intentionally not duplicated here.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v w

/-- **Sentence 102.**  An injective endomorphism of a finite-dimensional
commutant is surjective. -/
theorem manuscriptSentence102_commutant_injective_implies_surjective
    {H : Type u} {k : Type v} {W : Type w}
    [Group H] [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (rho : H →* (W ≃ₗ[k] W))
    (L : Subgroup H)
    {Phi : ↥(fixedSubmodule (adjointRep rho) L) →ₗ[k]
      ↥(fixedSubmodule (adjointRep rho) L)}
    (hPhi : Function.Injective Phi) :
    Function.Surjective Phi :=
  commutant_surjective_of_injective rho L hPhi

/-- **Sentence 105.**  Finite dimensionality is essential: the repository's
explicit infinite-dimensional shift conjugation is injective but not
surjective. -/
theorem manuscriptSentence105_finiteDimensionality_is_essential :
    CommutantFiniteDimensionalHypothesisIsEssential :=
  manuscriptCommutantFiniteDimensionalHypothesisIsEssential

/-- **Sentence 106.**  The analogous projection argument is carried by
one-sided Kazhdan projection order together with stable finiteness of norm
matrix coronas. -/
theorem manuscriptSentence106_projectionOrder_and_stableFiniteness :
    OneSidedKazhdanProjectionOrder ∧ NormMatrixCoronaStableFinite :=
  ⟨manuscriptOneSidedKazhdanProjectionOrder,
    manuscriptNormMatrixCoronaStableFinite⟩

/-- **Sentence 107.**  The squared normalized Hilbert--Schmidt norm is the
sum of the entrywise squared complex norms divided by the matrix dimension. -/
theorem manuscriptSentence107_normalizedHilbertSchmidt_formula
    (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsNormSq Y A =
      (∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) / Fintype.card Y :=
  rfl

/-- **Sentence 110.**  Operator norm dominates normalized
Hilbert--Schmidt norm in every positive finite dimension. -/
theorem manuscriptSentence110_operatorNorm_defect_implies_HS_defect
    (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (A : Matrix Y Y ℂ) :
    hsNormSq Y A ≤ ‖A‖ * ‖A‖ :=
  hsNormSq_le_mul_self_l2_opNorm Y hY A

/-- **Sentences 112--113.**  The shadow residual is exactly the intersection
of all normalized Hilbert--Schmidt kernels, with its universal membership
criterion. -/
theorem manuscriptSentences112_113_shadowResidual_intersection :
    ShadowResidualIsIntersectionOfHSKernels :=
  manuscriptShadowResidualIsIntersectionOfHSKernels

/-- **Sentences 114--115.**  Norm matrix coronas are stably finite, and
comparable unitarily equivalent projections in them are equal. -/
theorem manuscriptSentences114_115_normMatrixCorona_stableFinite :
    NormMatrixCoronaStableFinite :=
  manuscriptNormMatrixCoronaStableFinite

/-- **Sentence 117.**  Vanishing of both coordinate Gram defects gives
eventual invertibility, unitary polar correction, and norm convergence of the
correction to the original lift. -/
theorem manuscriptSentence117_polarCorrection
    {A : ℕ → Type*} [∀ n, CStarAlgebra (A n)] (x : ∀ n, A n)
    (h1 : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0))
    (h2 : Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) cofinite (nhds 0)) :
    (∀ᶠ n in cofinite, IsUnit (x n)) ∧
      (∀ᶠ n in cofinite,
        PolarLiftingGeneralCStar.polarUnitary (x n) ∈ unitary (A n)) ∧
      Tendsto (fun n ↦
        ‖PolarLiftingGeneralCStar.polarUnitary (x n) - x n‖)
        cofinite (nhds 0) :=
  FiniteBlockCorona.printedUnitaryLifting_sequence_cofinite x h1 h2

/-- **Sentences 118--120.**  Isometries are unitaries in every finite matrix
amplification of a norm matrix corona, and the corresponding projection
comparison holds in the base corona and all amplifications. -/
theorem manuscriptSentences118_120_stableFinite_order_package :
    NormMatrixCoronaStableFiniteOrder :=
  manuscriptStableFinite

/-- **Sentence 121.**  An isometry pair with the printed absorption relation
lies in the corner cut out by `q`. -/
theorem manuscriptSentence121_isometryPair_lies_in_corner
    {A : Type u} [CStarAlgebra A] {p q w : A}
    (hq : IsStarProjection q) (hqp : q * p = p)
    (hwstarw : star w * w = q) (hwwstar : w * star w = p) :
    q * w * q = w :=
  cstar_corner_eq_of_isometryPair hq hqp hwstarw hwwstar

/-- **Sentence 123.**  In a finite C-star algebra, comparable projections
implemented by an isometry pair are equal. -/
theorem manuscriptSentence123_comparable_equivalent_projections_equal
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q w : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hle : p ≤ q) (hwstarw : star w * w = q)
    (hwwstar : w * star w = p) :
    p = q :=
  eq_of_isometryPair_of_le hfinite hp hq hle hwstarw hwwstar

/-- **Sentence 125.**  One-sided compression gives the inverse-conjugated
Kazhdan projection order, in its order-instance-free absorption form. -/
theorem manuscriptSentence125_oneSidedKazhdanProjectionOrder :
    OneSidedKazhdanProjectionOrder :=
  manuscriptOneSidedKazhdanProjectionOrder

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
