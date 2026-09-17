import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The closed trio of the Below Greendlinger waist

`AsmWaist.closedTrio : ClosedTrioStatement` bundles the three hypothesis-free producers of the
closed residuals of the Below waist:

* residual 05, `OsinTwoGonCleanCopySectionStatement`: `Piece05.proof`;
* residual 08, `OsinSectionPocketFaceSetProperSectionStatement`: `P08ProperArc.proof`;
* residual 09, `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`: `Piece09.proof`.

It is this lane's local producer of the gl-assembly-01 interface (`AsmTrio.closedTrio`, not on disk
at authoring time).  It imports only the three producer modules, never `Assembly`, `Piece04/Proof`,
`Piece06/Proof`, `Piece07/Proof` or `Piece10/Proof`.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist

universe u w v

/-- **The three closed residuals of the Below Greendlinger waist hold**, with no hypotheses. -/
theorem closedTrio : ClosedTrioStatement.{u, w, v} :=
  ⟨Piece05.proof.{u, w, v}, P08ProperArc.proof.{u, w, v}, Piece09.proof.{u, w, v}⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.closedTrio
