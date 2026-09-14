import GroupApproximation.Dynamics.TwoEndedUnitGroup
import GroupApproximation.Algebra.FinitaryShiftLEF
import GroupApproximation.Meta.AxiomGuard

/-!
# The units of the two-ended crossed product are LEF

`non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget` (tex 1786–1792):

> This semidirect product is LEF: copy any finite table's finitary supports and the translated
> supports used in its products into a sufficiently long finite cycle [...]  Thus $R_X^\times$ is LEF
> although $\GL_3(R_X)$ is not MF\@.

`R_X^× ≅ GL_fin(ℤ, 𝔽₂) ⋊ ℤ` (`TwoEndedUnitGroup`), and the semidirect product is LEF
(`FinitaryGL.printedFinitaryShiftLEF`, lane ms-traces-3), so `R_X^×` is LEF.  Not MF of `GL_3(R_X)`
is `prop:bilateral-three` at `n = 3`, because `R_X` is not directly finite (`TwoEndedShift`).

* `printedTwoEndedUnitsLEF`: closed endpoint, `R_X^×` is LEF;
* `printedTwoEndedUnitsLEFGLThreeNotMF_of_bilateralThree`: the full sentence over
  `Manuscript.ChainCore.BilateralThree.PrintedBilateralThree` (lane ct-bilateral-mf).
-/

namespace GroupApproximation

namespace TwoEndedShift

/-- **tex 1791**: "Thus `R_X^×` is LEF", for `R_X = LC(X, 𝔽₂) ⋊_T ℤ` with `T` the shift on
`X = ℤ ∪ {−∞, +∞}`. -/
def PrintedTwoEndedUnitsLEF : Prop :=
  IsLEF (ClopenCrossedProduct shift (ZMod 2))ˣ

theorem printedTwoEndedUnitsLEF : PrintedTwoEndedUnitsLEF :=
  isLEF_of_injective unitsEquivFinitaryShift.toMonoidHom unitsEquivFinitaryShift.injective
    FinitaryGL.printedFinitaryShiftLEF

/-- **tex 1791–1792**: "Thus `R_X^×` is LEF although `GL_3(R_X)` is not MF", over
`prop:bilateral-three`. -/
theorem printedTwoEndedUnitsLEFGLThreeNotMF_of_bilateralThree (hB : Manuscript.ChainCore.BilateralThree.PrintedBilateralThree) :
    PrintedTwoEndedUnitsLEFGLThreeNotMF :=
  printedTwoEndedUnitsLEFGLThreeNotMF_of_pieces FinitaryGL.printedFinitaryShiftLEF hB

end TwoEndedShift

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.TwoEndedShift.printedTwoEndedUnitsLEF
#audit_axioms GroupApproximation.TwoEndedShift.printedTwoEndedUnitsLEFGLThreeNotMF_of_bilateralThree
