import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.LocAmenTraceEndpoint
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerClose
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-29, part 4: `NuclearLocallyAmenableTraceStatement`, unconditional

This file wires `locAmenTrace_nuclearLocallyAmenableTrace_of_contractionSqrt` to the
PowersStormer sibling lane's `NuclearDensity.powersStormer_contractionSqrtCommutator`.

It is kept separate from `LocAmenTraceEndpoint.lean` so that the endpoint does not depend
on the sibling's files.  If `PowersStormerClose` fails to build, only this file is affected.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearAmenable

noncomputable section

universe u

/-- **Every tracial state of a separable nuclear C⋆-algebra is locally amenable.** -/
theorem locAmenTrace_nuclearLocallyAmenableTraceStatement :
    NuclearLocallyAmenableTraceStatement.{u} :=
  locAmenTrace_nuclearLocallyAmenableTrace_of_contractionSqrt
    NuclearDensity.powersStormer_contractionSqrtCommutator

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_nuclearLocallyAmenableTraceStatement

end

end Manuscript.NonMF.TWWLanes.NuclearAmenable
end GroupApproximation
