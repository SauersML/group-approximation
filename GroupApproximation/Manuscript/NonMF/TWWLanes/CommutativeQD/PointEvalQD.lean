import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.Main
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.PointEval
import GroupApproximation.Meta.AxiomGuard

/-!
# Tracial states on separable commutative C⋆-algebras are quasidiagonal, unconditionally

`Main.lean` (lane `nm-tww-02`) proves the quasidiagonality of tracial states on separable
unital commutative C⋆-algebras over `hPE : PointEvaluationAverageStatement`. `PointEval.lean`
proves that statement (`pointEvaluationAverageStatement_holds`). This module discharges `hPE`
in the `Main.lean` endpoints. No hypothesis beyond those printed remains.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeQD

open WeakDual Quasidiagonal
open scoped ComplexOrder

universe u

/-- A unital linear functional with `τ(x⋆x) ≥ 0` on a separable commutative unital
C⋆-algebra is a quasidiagonal trace. -/
theorem pointEval_isQuasidiagonalTrace_of_commCStarAlgebra {A : Type u}
    [CommCStarAlgebra A] (hsep : TopologicalSpace.SeparableSpace A) (τ : A →ₗ[ℂ] ℂ)
    (hone : τ 1 = 1) (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commCStarAlgebra_of_pointEvaluationAverage
    pointEvaluationAverageStatement_holds hsep τ hone hpos

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEval_isQuasidiagonalTrace_of_commCStarAlgebra

/-- The same statement for a `CStarAlgebra` whose multiplication commutes. -/
theorem pointEval_isQuasidiagonalTrace_of_commutative {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    (τ : A →ₗ[ℂ] ℂ) (hone : τ 1 = 1) (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage
    pointEvaluationAverageStatement_holds hcomm τ hone hpos

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEval_isQuasidiagonalTrace_of_commutative

/-- **Every tracial state on a separable unital commutative C⋆-algebra is
quasidiagonal**, for a bundled `TracialState`. -/
theorem pointEval_isQuasidiagonalTrace_of_commutative_tracialState {A : Type u}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (hcomm : ∀ a b : A, a * b = b * a) (τ : TracialState A) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commutative_tracialState_of_pointEvaluationAverage
    pointEvaluationAverageStatement_holds hcomm τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEval_isQuasidiagonalTrace_of_commutative_tracialState

/-- The same for a bundled `FaithfulTracialState`. -/
theorem pointEval_isQuasidiagonalTrace_of_commutative_faithfulTracialState {A : Type u}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (hcomm : ∀ a b : A, a * b = b * a) (τ : FaithfulTracialState A) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commutative_faithfulTracialState_of_pointEvaluationAverage
    pointEvaluationAverageStatement_holds hcomm τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEval_isQuasidiagonalTrace_of_commutative_faithfulTracialState

/-- **Lane shape.** A tracial state `τ : A → ℂ` (`IsTracialState`) on a separable unital
commutative C⋆-algebra is a quasidiagonal trace. -/
theorem pointEval_isQuasidiagonalTrace_of_commutative_isTracialState {A : Type u}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (hcomm : ∀ a b : A, a * b = b * a) {τ : A → ℂ} (hτ : IsTracialState τ) :
    IsQuasidiagonalTrace τ :=
  isQuasidiagonalTrace_of_commutative_isTracialState_of_pointEvaluationAverage
    pointEvaluationAverageStatement_holds hcomm hτ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEval_isQuasidiagonalTrace_of_commutative_isTracialState

end CommutativeQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
