import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEJZInstance
import GroupApproximation.Meta.AxiomGuard

/-!
# The Ershov--Jaikin-Zapirain input used in `Non-MF Groups`

The manuscript invokes the Ershov--Jaikin-Zapirain property-`(T)` theorem only
for the binary Leavitt algebra `R = L_{ᵓ₂}(1,2)`, at ranks twelve and
three. These are exactly the two conclusions packaged below.

The proof is internal: `RankTwelveEJZInstance` applies the repository's
finite-field elementary-group theorem to the finite-type `ZMod 2`-algebra
`R`, and transports the rank-three result to the upper-left corner subgroup.
The literature citation in the manuscript therefore records provenance; it is
not an axiom of the formal development.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace PriorWork

/-- The two property-`(T)` conclusions for the groups occurring in the
Leavitt compression proposition: `H = EL₁₂(R)` and its embedded
rank-three corner. -/
theorem ershovJaikinZapirain_binaryLeavitt_application :
    HasKazhdanPropertyT.{0, 0}
        OneSidedMFRadical.RankTwelveEndpoint.H ∧
      HasKazhdanPropertyT.{0, 0}
        OneSidedMFRadical.RankTwelveEndpoint.corner :=
  OneSidedMFRadical.RankTwelveEndpoint.printedBothGroupsHaveKazhdanPropertyT

end PriorWork
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMF.PriorWork.ershovJaikinZapirain_binaryLeavitt_application
