import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Gaps
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.OuterPinch
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger leaf over exactly the in-flight frontier Statements

Lane gl-assembly-03 endpoint.  The five-binder Below waist of lane gl-assembly-02,
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow` (`AsmWaist/Endpoint`),
is fed with the frontier reductions of `AsmFrontier/Gaps` and `AsmFrontier/OuterPinch`:

| residual | binder | frontier Statements |
|---|---|---|
| 01 | `hbudget` | `OsinLemma94ClassEndLoopsBudgetInput` itself |
| 04 | `hspan` | `Piece04.ClassPocketRotationTurnStatement` |
| 06 | `hcellStep` | `Piece06.CornerRefine.MonogonCornerStatement`, `Piece06.CellRoseUncutLakesBelowStatement` |
| 07 | `hproper` | `P07LakeExclusion.CellPocketInnerTwoArcLongStatement` |
| 10 | `hstep` | `P10ChordLift.NonRoseStepStatement`, `P10Rose.RoseRegionMoveSubArcStatement` |

* `openResidualsBelow_of_frontier`: the bundled `AsmWaist.GreendlingerOpenResidualsBelowStatement`
  from the seven frontier Statements.
* `relativeGreendlingerQuasiGeodesicLeastArea_of_frontier`: Osin's Lemma 4.4 at least-area diagrams
  from the seven frontier Statements.

The lane names the hypothesis `hmono` with the type `Piece06.MonogonCornerStatement`; that
declaration lives in the namespace `Piece06.CornerRefine`, and the binder uses its real name.

This is a Statement-hypothesis audit theorem (an interface), not a census endpoint.  Each hypothesis
is an open region-level Statement; the target is true (Osin's Lemma 4.4).

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

universe u w v

/-- **The five open residuals of the Below waist from the frontier Statements.** -/
theorem openResidualsBelow_of_frontier
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hmono : Piece06.CornerRefine.MonogonCornerStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hinner : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v})
    (hnon : P10ChordLift.NonRoseStepStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    AsmWaist.GreendlingerOpenResidualsBelowStatement.{u, w, v} :=
  ⟨hbudget, gapSpan_of_rotationTurns hrot, cellStepBelow_of_monogonCorner_lakes hmono hlakes,
    properArcsBelow_of_innerTwoArcLong hinner, outerPinchStep_of_nonRose_subArc hnon hsub⟩

/-- **Osin's Lemma 4.4 at least-area diagrams from the frontier Statements**: the budget input, the
rotation turns of a class pocket, the monogon corner, the uncut lakes below, the long inner two-arc,
the non-rose outer-pinch step and the sub-arc region move of the rose case. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_frontier
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hmono : Piece06.CornerRefine.MonogonCornerStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hinner : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v})
    (hnon : P10ChordLift.NonRoseStepStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow hbudget
    (gapSpan_of_rotationTurns hrot) (cellStepBelow_of_monogonCorner_lakes hmono hlakes)
    (properArcsBelow_of_innerTwoArcLong hinner) (outerPinchStep_of_nonRose_subArc hnon hsub)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.openResidualsBelow_of_frontier
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_frontier
