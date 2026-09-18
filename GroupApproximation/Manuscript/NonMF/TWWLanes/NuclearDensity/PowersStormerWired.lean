import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerClose
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseEndpoint
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosUcpReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Powers--Størmer, wired: the `sqrtControl` field is unconditional

Lane nm-tww-26d proves `ContractionSqrtCommutatorStatement` outright
(`powersStormer_contractionSqrtCommutator`). This file discharges the `hsqrt` hypothesis of
the lane nm-tww-25 and nm-tww-28c endpoints, so that the only remaining input for
`NuclearDensityGapStatement` is the CPAP side.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

noncomputable section

universe u

/-- `HasSqrtCommutatorControl A` holds on every unital C⋆-algebra `A`, unconditionally. -/
theorem powersStormerWired_hasSqrtCommutatorControl (A : Type u) [CStarAlgebra A] :
    HasSqrtCommutatorControl A :=
  hasSqrtCommutatorControl_of_contraction powersStormer_contractionSqrtCommutator A

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormerWired_hasSqrtCommutatorControl

/-- The lane nm-tww-25 endpoint with `hsqrt` discharged. -/
theorem powersStormerWired_nuclearDensityGapStatement
    (hcpap : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → IsMatrixLeftBimoduleCPAP A) :
    NuclearDensityGapStatement.{u} :=
  nuclearDensityGapStatement_of_close hcpap powersStormer_contractionSqrtCommutator

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormerWired_nuclearDensityGapStatement

/-- The nuclear trace density interface from the CPAP side alone. -/
theorem powersStormerWired_nuclearTraceApproxDensityStatement
    (hcpap : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → IsMatrixLeftBimoduleCPAP A) :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  nuclearTraceApproxDensityStatement_of_close hcpap powersStormer_contractionSqrtCommutator

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormerWired_nuclearTraceApproxDensityStatement

/-- The lane nm-tww-28c endpoint with `hsqrt` discharged: only the UCP Kraus Statement remains. -/
theorem powersStormerWired_ucp_nuclearTraceApproxDensityStatement
    (hkraus : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → ChoiEffrosUcpKrausStatement A) :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  choiEffrosUcp_nuclearTraceApproxDensityStatement hkraus
    powersStormer_contractionSqrtCommutator

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormerWired_ucp_nuclearTraceApproxDensityStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
