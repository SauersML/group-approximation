import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.Endpoint
import GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros into matrix-sequence coronas: discharging the `nm-tww-09` interface

Lane `nm-tww-09` recorded the output of this lane as the proposition
`LiftCriterion.CoronaUCPCoordinatesStatement`. It proved
`isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates` from that proposition.

This file proves the proposition unconditionally. The proof applies
`exists_ucpCoordinates_of_starHom_normMatrixCorona`, whose conclusion is the same
existential word for word.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CoronaChoiEffros

universe u

/-- **The `nm-tww-08` interface holds.** -/
theorem coronaUCPCoordinatesStatement : LiftCriterion.CoronaUCPCoordinatesStatement.{u} := by
  unfold LiftCriterion.CoronaUCPCoordinatesStatement
  intro A _ _ hnuc X _ Φ
  exact exists_ucpCoordinates_of_starHom_normMatrixCorona A hnuc X Φ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.coronaUCPCoordinatesStatement

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
