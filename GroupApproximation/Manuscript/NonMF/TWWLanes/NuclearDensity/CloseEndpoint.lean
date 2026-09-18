import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.Reduction
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseCPAPReduction
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseSqrtReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-25, part 6: the endpoint

Both fields of `NuclearDensityGapStatement` are true.  Neither closes in the corpus, so each
is reduced to one strictly smaller true Statement:

* `cpap` reduces to `IsMatrixLeftBimoduleCPAP`, which is `IsMatrixCPAP` without the right
  bimodule clause and without both multiplicativity clauses (`CloseCPAPReduction`);
* `sqrtControl` reduces to `ContractionSqrtCommutatorStatement`, which is Powers--Størmer
  control for a single contraction on a single matrix space (`CloseSqrtReduction`).

This file assembles the gap Statement from the two smaller Statements, and composes the
result with the lane nm-tww-12 endpoint.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **The lane nm-tww-25 endpoint.**  The two smaller Statements give
`NuclearDensityGapStatement`. -/
theorem nuclearDensityGapStatement_of_close
    (hcpap : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → IsMatrixLeftBimoduleCPAP A)
    (hsqrt : ContractionSqrtCommutatorStatement) : NuclearDensityGapStatement.{u} :=
  ⟨fun A inst hn ↦ @isMatrixCPAP_of_leftBimodule A inst (hcpap A inst hn),
    fun A inst ↦ @hasSqrtCommutatorControl_of_contraction hsqrt A inst⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.nuclearDensityGapStatement_of_close

/-- **The composite.**  The two smaller Statements give the nuclear trace density interface
`NuclearAmenable.NuclearTraceApproxDensityStatement`. -/
theorem nuclearTraceApproxDensityStatement_of_close
    (hcpap : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → IsMatrixLeftBimoduleCPAP A)
    (hsqrt : ContractionSqrtCommutatorStatement) :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  nuclearTraceApproxDensityStatement_of_nuclearDensityGapStatement
    (nuclearDensityGapStatement_of_close hcpap hsqrt)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.nuclearTraceApproxDensityStatement_of_close

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
