import GroupApproximation.Matching.EssentialExpanderRepair
import GroupApproximation.KunThom.KunThomTheorem

/-!
# Kun--Thom for an essential expander certificate

The selected graph is first repaired to an exact expanding action, after which
the internally proved exact-expander theorem applies.  The caller supplies
only mathematical data, never a theorem-shaped callback.
-/

namespace GroupApproximation
namespace KunThomEssential

open EssentialExpanderRepair

variable {K J : Type} [Group K] [Group J]

/-- A `MatchingCertificate`, together with actual Kazhdan-pair data for its
first factor, forces the commuting factor to be LEF. -/
theorem isLEF_of_matchingCertificate
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ)
    (C : MatchingCertificate K J)
    (S : Finset K) (hQS : Q ⊆ S) (hKS : C.generatorsK ⊆ S)
    (hone : 1 ∈ S) (hκone : κ ≤ 1)
    : IsLEF J := by
  apply KunThomTheorem.isLEF_of_exactProductExpansion hQ S hQS hone hκone
    (repairedApproximation C) (expansionConstant_pos C)
  exact repairedDirected_expands_eventually C S hKS

end KunThomEssential
end GroupApproximation
