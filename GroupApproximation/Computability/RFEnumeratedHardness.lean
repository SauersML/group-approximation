import GroupApproximation.Computability.RFPresentationPi02
import GroupApproximation.Computability.SoficRecognitionSecondLevel

/-!
# Residual finiteness is second-level hard on enumerated presentations

Residual finiteness is hereditary, holds for the trivial group, and fails
for the finitely presented nonsofic group (residually finite groups are
sofic), so the hereditary switch of
`Computability.SoficRecognitionSecondLevel` applies: on enumerated
presentation codes residual finiteness is `Π⁰₂`-hard and its failure
`Σ⁰₂`-hard.  The exact level is `Π⁰₃` (research node
`residual-finiteness-of-enumerated-presentations-is-pi3-complete`); the
third level is a group-theoretic argument not formalized here.  This file
records the machine-checked second-level lower bound.
-/

namespace GroupApproximation
namespace RFEnumeratedHardness

open PresentationCodes SoficRecognitionSecondLevel RFPresentationPi02

/-- Residual finiteness of enumerated presentation codes is `Π⁰₂`-hard. -/
theorem rfCode_pi02Hard :
    ArithmeticalHierarchy.Pi02Hard
      (fun q : EnumeratedPresentationCodes.PresentationCode ↦
        Group.ResiduallyFinite (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, hseed⟩ := exists_non_residuallyFinite_code
  exact pi02Hard_of_hereditary (fun (H : Type) (_ : Group H) ↦ Group.ResiduallyFinite H)
    (fun f hf hK ↦ by
      haveI := hK
      exact residuallyFinite_of_injective f hf)
    (by
      haveI := residuallyFinite_trivialCode
      exact residuallyFinite_of_injective (1 : PUnit →* Carrier trivialCode)
        (fun a b _ ↦ Subsingleton.elim a b))
    seed hseed

end RFEnumeratedHardness
end GroupApproximation
