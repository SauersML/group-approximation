import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGeneratedCore

/-!
# Trace formulas for tensor synchronization
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open Filter

noncomputable section

universe u v w

noncomputable local instance tensorTracePartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorTraceStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The normalized coordinate traces of every nonidentity product element
are eventually zero. -/
theorem synchronizedCoordinateTrace_eventually_zero
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)] [∀ n, Nonempty (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n)
    (hdetect : ∀ z : Gamma × Q, z.1 = 1 → z.2 ≠ 1 →
      ∀ᶠ n in cofinite, ell n z ≠ 1)
    (z : Gamma × Q) (hz : z ≠ 1) :
    ∀ᶠ n in cofinite,
      matrixTracialState R.tau (E n) (inferInstance : Nonempty (E n))
        (synchronizedCoordinateHom E R ell n z :
          TensorCoordinateAlgebra A E n) = 0 := by
  by_cases hfirst : z.1 = 1
  · have hsecond : z.2 ≠ 1 := by
      intro hsecond
      apply hz
      exact Prod.ext hfirst hsecond
    filter_upwards [hdetect z hfirst hsecond] with n hn
    exact finiteProductTensorHom_trace_zero_of_finite_ne_one
      (inferInstance : Nonempty (E n)) R.rho R.tau (ell n) z hn
  · exact Filter.Eventually.of_forall fun n ↦
      finiteProductTensorHom_trace_zero_of_first_ne_one
        (inferInstance : Nonempty (E n)) R (ell n) z hfirst

/-- The eventual trace-zero formula in the exact finite-quotient language of
the manuscript. -/
theorem manuscriptSynchronizedCoordinateTrace_eventually_zero
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A]
    (G B : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (B n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (B n)]
    [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (B n)]
    (R : RegularRealizationData Gamma A)
    (lambda : ∀ n, Gamma →* G n) (beta : ∀ n, Q →* B n)
    (hdetect : ∀ q : Q, q ≠ 1 → ∀ᶠ n in cofinite, beta n q ≠ 1)
    (z : Gamma × Q) (hz : z ≠ 1) :
    ∀ᶠ n in cofinite,
      matrixTracialState R.tau (G n × B n)
        (inferInstance : Nonempty (G n × B n))
        (synchronizedCoordinateHom (fun n ↦ G n × B n) R
          (fun n ↦ productFiniteQuotientHom (lambda n) (beta n)) n z :
          TensorCoordinateAlgebra A (fun n ↦ G n × B n) n) = 0 := by
  exact synchronizedCoordinateTrace_eventually_zero
    (fun n ↦ G n × B n) R
    (fun n ↦ productFiniteQuotientHom (lambda n) (beta n))
    (fun z hfirst hsecond ↦
      productFiniteQuotient_eventually_detects_second
        lambda beta hdetect z hfirst hsecond)
    z hz

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
