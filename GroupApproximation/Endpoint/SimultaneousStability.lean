import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Stability.MixedApproximation

/-!
# Simultaneous P-stability and operator-norm stability endpoint

This file joins the two unconditional non-approximability witnesses already
proved in the repository.  Their direct product is neither sofic nor
operator-MF in the mixed-family sense.

Only closed results are exported.  In particular, this file does not package
Fournier--Facio Propositions B/C as a hypothesis and does not state the final
existence theorem until their construction is formalized in the repository.
-/

namespace GroupApproximation

open ChosenNonMFTheorem

/-- The direct product of the explicit universal-Leavitt nonsofic group and
the explicit countable Clifford-compression non-operator-MF group. -/
abbrev SimultaneousStabilitySeed : Type :=
  UniversalRankFour.Ambient × MarkedCompression.Explicit.theGroup

/-- The repository's two unconditional endpoints rule out the single mixed
approximation family on the direct-product seed. -/
theorem simultaneousStabilitySeed_not_isMixedApproximable :
    ¬ IsMixedApproximable SimultaneousStabilitySeed :=
  not_isMixedApproximable_prod universalLeavittEL4_not_isSofic
    countableWitness_not_isOperatorMF

end GroupApproximation
