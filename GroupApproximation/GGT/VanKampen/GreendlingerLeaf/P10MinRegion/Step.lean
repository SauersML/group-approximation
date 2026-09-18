import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The Piece10 outer-pinch step from the extremal-region statement

Lane gl-p10-89.

The no-wrap outer-pinch step `P10ExtremalWrap.PocketOuterPinchStepSectionNoWrapStatement`
(the `hstep` of `P10ExtremalWrap.relativeGreendlinger_of_binderFiveBelowNoWrap`) follows from
`P10ExtremalRegion.RoseExtremalRegionStatement` through its existing Piece10Live consumers
`P10ExtremalRegion.blockNoWrap_of_extremalRegion`,
`P10ExtremalWrap.contigResidualNoWrap_of_blockNoWrap` and
`P10ExtremalWrap.stepNoWrap_of_contigResidualNoWrap`.

LOUD: this wiring is VACUOUS at universes `0, 0, 0`.  Its premise is refuted by
`p10MinRegion_not_extremalRegion` (`P10MinRegion/Refute`), so it closes no gap; it records only
that the Piece10Live consumer chain type-checks from the target.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **The no-wrap outer-pinch step from the extremal-region statement** (vacuous: the premise is
false, `p10MinRegion_not_extremalRegion`). -/
theorem p10MinRegion_stepNoWrap_of_extremalRegion
    (h : P10ExtremalRegion.RoseExtremalRegionStatement.{u, w, v}) :
    P10ExtremalWrap.PocketOuterPinchStepSectionNoWrapStatement.{u, w, v} :=
  P10ExtremalWrap.stepNoWrap_of_contigResidualNoWrap
    (P10ExtremalWrap.contigResidualNoWrap_of_blockNoWrap
      (P10ExtremalRegion.blockNoWrap_of_extremalRegion h))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p10MinRegion_stepNoWrap_of_extremalRegion

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
