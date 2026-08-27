import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration

/-!
# The displayed definition and invertibility of `tau`

This file gives census row 213 its standalone exact declaration.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-- **Sentence-census row 213.**  The raw matrix `tau` is `diag(X,Y)`, its
printed inverse is `diag(Y,X)`, both inverse products are identities, and its
flattened unit is the literal element of `GL₁₂(R)` used thereafter. -/
theorem manuscriptTauDefinitionAndInvertibility :
    RankTwelve.tau leavittFamily =
        !![RankTwelve.shift leavittFamily, 0;
          0, RankTwelve.shiftInv leavittFamily] ∧
      RankTwelve.tauInv leavittFamily =
        !![RankTwelve.shiftInv leavittFamily, 0;
          0, RankTwelve.shift leavittFamily] ∧
      RankTwelve.tau leavittFamily * RankTwelve.tauInv leavittFamily = 1 ∧
      RankTwelve.tauInv leavittFamily * RankTwelve.tau leavittFamily = 1 ∧
      IsUnit (RankTwelve.tau leavittFamily) ∧
      (RankTwelve.tauUnit leavittFamily : RankTwelve.Full R) =
        RankTwelve.tau leavittFamily ∧
      printedTauGL = flat12Units (RankTwelve.tauUnit leavittFamily) := by
  exact ⟨rfl, rfl,
    RankTwelve.tau_mul_tauInv leavittFamily,
    RankTwelve.tauInv_mul_tau leavittFamily,
    ⟨RankTwelve.tauUnit leavittFamily, rfl⟩,
    RankTwelve.tauUnit_val leavittFamily,
    printedTauGL_eq_flat12Units⟩

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
