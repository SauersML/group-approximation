import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration

/-!
# The Whitehead conclusion for the printed stable letter

This file gives census row 216 one exact declaration: it retains the two
inverse equations `XY = YX = 1`, the literal six-factor equality, the
flattening equation, and the resulting membership in `EL₁₂(R)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-- **Sentence-census row 216.**  Since the printed `Y` is the inverse of
`X`, the six-factor Whitehead identity is the printed `tau`; after flattening,
that unit belongs to the elementary group. -/
theorem manuscriptTauElementaryViaWhiteheadFactorization :
    RankTwelve.shift leavittFamily * RankTwelve.shiftInv leavittFamily = 1 ∧
      RankTwelve.shiftInv leavittFamily * RankTwelve.shift leavittFamily = 1 ∧
      RankTwelve.tauUnit leavittFamily =
        elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
          elementaryUnit 1 0 (by decide)
            (-(RankTwelve.shiftInv leavittFamily)) *
          elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
          elementaryUnit 1 0 (by decide) 1 *
          elementaryUnit 0 1 (by decide) (-1) *
          elementaryUnit 1 0 (by decide) 1 ∧
      printedTauGL = flat12Units (RankTwelve.tauUnit leavittFamily) ∧
      printedTauGL ∈ elementaryGroup (Fin 12) R := by
  exact ⟨RankTwelve.shift_mul_shiftInv leavittFamily,
    RankTwelve.shiftInv_mul_shift leavittFamily,
    tauUnit_eq_six_elementary,
    printedTauGL_eq_flat12Units,
    printedTauGL_mem⟩

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
