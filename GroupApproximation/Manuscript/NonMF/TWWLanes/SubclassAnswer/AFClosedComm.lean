import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.Main
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.PointEval
import GroupApproximation.Meta.AxiomGuard

/-!
# The last `PointEvaluationAverageStatement` consumer, discharged (lane `nm-tww-35`)

`CommutativeQD/Main.lean` (lane `nm-tww-02`) has six endpoints taking
`hPE : CommutativeQD.PointEvaluationAverageStatement.{u}`. `CommutativeQD/PointEvalQD.lean`
discharges five of them. The sixth,
`CommutativeQD.isQuasidiagonalTrace_of_commutative_clm_of_pointEvaluationAverage`
(continuous-functional form), is discharged here with
`CommutativeQD.pointEvaluationAverageStatement_holds` (`CommutativeQD/PointEval.lean`).

Neither imported module imports an `AFClosed*` module, so there is no cycle.

## Truth check

A positive unital functional on a separable unital commutative C⋆-algebra `C(X)` is a
probability measure on `X`, hence a weak⋆ limit of rational averages of point evaluations;
each average is the normalized trace of a diagonal unital ⋆-homomorphism into `M_N(ℂ)`.
True, no remaining gap.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

open scoped ComplexOrder

universe u

/-- **Continuous-functional form, unconditional.** A continuous unital functional `τ` with
`τ(x⋆x) ≥ 0` on a separable unital C⋆-algebra whose multiplication commutes is a
quasidiagonal trace. -/
theorem afClosed_isQuasidiagonalTrace_of_commutative_clm {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    (τ : A →L[ℂ] ℂ) (hone : τ 1 = 1) (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  CommutativeQD.isQuasidiagonalTrace_of_commutative_clm_of_pointEvaluationAverage
    CommutativeQD.pointEvaluationAverageStatement_holds hcomm τ hone hpos

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.afClosed_isQuasidiagonalTrace_of_commutative_clm
