import GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.Interfaces
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.Main
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.PointEval
import GroupApproximation.Meta.AxiomGuard

/-!
# `CommutativeQuasidiagonalTraceStatement` holds (lane `nm-tww-33`)

`Interfaces.lean` (lane `nm-tww-05`) records the interface

> every faithful tracial state on a separable unital commutative C⋆-algebra is
> quasidiagonal

as the proposition `CommutativeQuasidiagonalTraceStatement`. This module proves it
unconditionally.

## Route

1. `CommutativeQD.isQuasidiagonalTrace_of_commutative_faithfulTracialState_of_pointEvaluationAverage`
   (lane `nm-tww-02`, `CommutativeQD/Main.lean`) derives the conclusion for a bundled
   `FaithfulTracialState` on a separable `CStarAlgebra` with commuting multiplication from
   `CommutativeQD.PointEvaluationAverageStatement.{u}`. That proof goes through Gelfand
   duality and a diagonal `⋆`-homomorphism model. Faithfulness is not used.
   The universe is `u = 0` here, because the interface quantifies over `A : Type`.
2. `CommutativeQD.pointEvaluationAverageStatement_holds` (lane `nm-tww-32`,
   `CommutativeQD/PointEval.lean`) proves `PointEvaluationAverageStatement.{u}` for every `u`
   from `CommutativeAverage.exists_pointEvaluation_average` (lane `nm-tww-01`). That proof uses
   a partition of unity and rational rounding, with no literature input.

## Endpoints

* `commQDTrace_of_pointEvaluationAverage`: the reduction
  `PointEvaluationAverageStatement.{0} → CommutativeQuasidiagonalTraceStatement`.
* `commQDTrace_holds : CommutativeQuasidiagonalTraceStatement`, unconditional.

## Truth check

The statement is true. On `C(X)` a state is a weak⋆ limit of rational averages of point
evaluations, and each average `a ↦ N⁻¹ ∑ᵢ xᵢ(a)` is the normalized trace of the unital
`⋆`-homomorphism `a ↦ diag(x₁(a), …, x_N(a))` into `M_N(ℂ)`. There is no remaining gap.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace SubclassAnswer

/-- **Reduction to the point-evaluation interface.** The interface of lane `nm-tww-01`
(at universe `0`) implies `CommutativeQuasidiagonalTraceStatement`. -/
theorem commQDTrace_of_pointEvaluationAverage
    (hPE : CommutativeQD.PointEvaluationAverageStatement.{0}) :
    CommutativeQuasidiagonalTraceStatement := by
  unfold CommutativeQuasidiagonalTraceStatement
  intro A _ _ hcomm τ
  exact
    CommutativeQD.isQuasidiagonalTrace_of_commutative_faithfulTracialState_of_pointEvaluationAverage
      hPE hcomm τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_of_pointEvaluationAverage

/-- **Every faithful tracial state on a separable unital commutative C⋆-algebra is
quasidiagonal.** This is `CommutativeQuasidiagonalTraceStatement`, unconditionally. -/
theorem commQDTrace_holds : CommutativeQuasidiagonalTraceStatement :=
  commQDTrace_of_pointEvaluationAverage
    CommutativeQD.pointEvaluationAverageStatement_holds.{0}

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_holds

/-- The unbundled form. A faithful tracial state `τ` on a separable unital C⋆-algebra
`A : Type` whose multiplication commutes is a quasidiagonal trace. -/
theorem commQDTrace_isQuasidiagonalTrace {A : Type} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) (hcomm : ∀ a b : A, a * b = b * a)
    (τ : FaithfulTracialState A) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  commQDTrace_holds A hsep hcomm τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.SubclassAnswer.commQDTrace_isQuasidiagonalTrace

end SubclassAnswer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
