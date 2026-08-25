import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedLeavittEquations

/-!
# The displayed shift matrices

The broad compressor-equations package contains the formulas in census rows
211--212.  This file gives each manuscript sentence its own declaration.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-- **Sentence-census row 211, the displayed matrix `X`.** -/
theorem manuscriptShiftMatrixX :
    RankTwelve.shift leavittFamily =
      !![RankTwelve.kap leavittFamily.s0,
          RankTwelve.kap (leavittFamily.s1 * leavittFamily.t0);
        0, RankTwelve.kap leavittFamily.t1] :=
  rfl

/-- **Sentence-census row 211, the displayed matrix `Y`.** -/
theorem manuscriptShiftMatrixY :
    RankTwelve.shiftInv leavittFamily =
      !![RankTwelve.kap leavittFamily.t0, 0;
        RankTwelve.kap (leavittFamily.s0 * leavittFamily.t1),
          RankTwelve.kap leavittFamily.s1] :=
  rfl

/-- **Sentence-census row 212.**  The displayed matrices satisfy both inverse
equations, and the bundled inverse of `X` has value exactly the displayed
`Y`. -/
theorem manuscriptShiftMatricesAreMutualInverses :
    RankTwelve.shift leavittFamily * RankTwelve.shiftInv leavittFamily = 1 ∧
      RankTwelve.shiftInv leavittFamily * RankTwelve.shift leavittFamily = 1 ∧
      ((RankTwelve.shiftUnit leavittFamily)⁻¹ :
          (RankTwelve.Half R)ˣ).val = RankTwelve.shiftInv leavittFamily := by
  exact ⟨RankTwelve.shift_mul_shiftInv leavittFamily,
    RankTwelve.shiftInv_mul_shift leavittFamily,
    RankTwelve.shiftUnit_inv_val leavittFamily⟩

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
