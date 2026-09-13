import GroupApproximation.Manuscript.ChainCore.BilateralThreeTransfer
import GroupApproximation.Manuscript.ChainCore.BilateralThreeCellDischarge
import GroupApproximation.Manuscript.ChainCore.ClopenCrossedProductCountableConsumers
import GroupApproximation.Dynamics.ClopenCrossedProductCountable
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:bilateral-three` over its two remaining pieces

Two of the four pieces of `printedBilateralThree_of_pieces` are now closed on main:

* `BilateralThreeCellStatement`, the three-coordinate cell (tex 1550–1593):
  `bilateralThreeCellStatement` (lane ct-bilateral-cell);
* `ClopenCrossedProductCountableStatement`, `R_X` countable (tex 1647–1649):
  `clopenCrossedProductCountableStatement` (lane ms-core-4), from
  `ClopenCrossedProduct.countable`.

So `prop:bilateral-three` rests only on Theorem `thm:core-ring-reflection` ("directly finite ⇒
LEF") and "if `R_X` is not directly finite, some defect is nonzero" (tex 1599–1602), and the
transfer piece of `cor:dynamic-rank-budget` rests only on the second.

* `printedBilateralThree_of_reflection`;
* `bilateralThreeTransferStatement_of_nonzeroDefect`.
-/

namespace GroupApproximation
namespace Manuscript
namespace ChainCore
namespace BilateralThree

/-- **`prop:bilateral-three` over "directly finite ⇒ LEF" and "not directly finite ⇒ a nonzero
defect"** (tex 1599–1602), with the cell and countability supplied by their closed producers. -/
theorem printedBilateralThree_of_reflection
    (hlef : ClopenCrossedProductDirectlyFiniteLEFStatement)
    (hdef : ClopenCrossedProductNonzeroDefectStatement) : PrintedBilateralThree :=
  printedBilateralThree_of_pieces bilateralThreeCellStatement
    GroupApproximation.clopenCrossedProductCountableStatement hlef hdef

/-- **The transfer piece of `cor:dynamic-rank-budget` over "not directly finite ⇒ a nonzero
defect"** (tex 1599–1600, 1763–1765), with the cell and countability supplied by their closed
producers. -/
theorem bilateralThreeTransferStatement_of_nonzeroDefect
    (hdef : ClopenCrossedProductNonzeroDefectStatement) :
    GroupApproximation.ChainCore.DynamicRankBudget.BilateralThreeTransferStatement :=
  bilateralThreeTransferStatement_of_pieces bilateralThreeCellStatement
    (fun _ _ _ _ T k _ _ => GroupApproximation.ClopenCrossedProduct.countable T k) hdef

end BilateralThree
end ChainCore
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.printedBilateralThree_of_reflection
#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.bilateralThreeTransferStatement_of_nonzeroDefect
