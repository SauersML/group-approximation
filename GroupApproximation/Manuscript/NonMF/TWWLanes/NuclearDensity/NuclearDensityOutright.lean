import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.LocAmenTraceEndpoint
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerWired
import GroupApproximation.Meta.AxiomGuard

/-!
# Nuclear density, unconditional

Lane nm-tww-29 proves the UCP Kraus Statement for every nuclear C⋆-algebra
(`NuclearAmenable.locAmenTrace_ucpKraus_of_isNuclear`), and lane nm-tww-26d proves
`ContractionSqrtCommutatorStatement` outright. Feeding both into the lane nm-tww-28c
reduction closes `NuclearDensityGapStatement` and the nuclear trace density interface.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

noncomputable section

universe u

/-- The UCP Kraus hypothesis of lane nm-tww-28c, discharged for every nuclear algebra. -/
theorem nuclearDensityOutright_hkraus : ∀ (A : Type u) (_ : CStarAlgebra A),
    CStarExactness.IsNuclearCStarAlgebra A → ChoiEffrosUcpKrausStatement A :=
  fun _ _ hn ↦ NuclearAmenable.locAmenTrace_ucpKraus_of_isNuclear hn

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.nuclearDensityOutright_hkraus

/-- `NuclearDensityGapStatement`, with no hypotheses. -/
theorem nuclearDensityOutright_nuclearDensityGapStatement : NuclearDensityGapStatement.{u} :=
  choiEffrosUcp_nuclearDensityGapStatement nuclearDensityOutright_hkraus
    powersStormer_contractionSqrtCommutator

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.nuclearDensityOutright_nuclearDensityGapStatement

/-- The nuclear trace density interface, with no hypotheses. -/
theorem nuclearDensityOutright_nuclearTraceApproxDensityStatement :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  powersStormerWired_ucp_nuclearTraceApproxDensityStatement nuclearDensityOutright_hkraus

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.nuclearDensityOutright_nuclearTraceApproxDensityStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
