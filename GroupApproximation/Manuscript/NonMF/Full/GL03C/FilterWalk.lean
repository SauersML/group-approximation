import GroupApproximation.Manuscript.NonMF.Full.GL03C.JunctionReduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Refute
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# GL03C filter walk: REFUTED, together with the surviving weaker residual

`Full/GL03C/Endpoint.lean` expects this module to provide
`roseFilterWalk : RoseFilterWalkStatement`.  **That statement is false.**
`roseExtremalJunction_of_filterWalk` proves that it implies
`P10RoseExtremalTrim.RoseExtremalJunctionStatement`, and
`roseJunctionRefute_not_junction` refutes that statement at universes `{0, 0, 0}`.
`glFix01_not_roseFilterWalk` records the refutation, so `roseFilterWalk` is deliberately
NOT provided here.

The strictly weaker true residual is the existing open statement
`P10Rose.RoseRegionMoveSubArcStatement`.  `glFix01_regionMoveSubArc_of_filterWalk` shows
that the filter walk implies it, through the junction and the single-region move.  It is
not refuted, and it still yields Piece 10 by `Piece10.proof_of_regionMoveSubArc`.
Downstream code should use that residual in place of `roseFilterWalk`.
-/

namespace GroupApproximation.Full.GL03C

open GroupApproximation.GGT.VanKampen

universe u w v

/-- The filter walk demanded by `GL03C/Endpoint.lean` fails at universes `{0, 0, 0}`,
because it implies the refuted extremal junction. -/
theorem glFix01_not_roseFilterWalk : ¬ RoseFilterWalkStatement.{0, 0, 0} := fun h =>
  GreendlingerLeaf.roseJunctionRefute_not_junction (roseExtremalJunction_of_filterWalk h)

#audit_axioms GroupApproximation.Full.GL03C.glFix01_not_roseFilterWalk

/-- The filter walk implies the open, unrefuted region-move sub-arc residual, which is
therefore strictly weaker.  This is the residual that downstream code should target. -/
theorem glFix01_regionMoveSubArc_of_filterWalk (h : RoseFilterWalkStatement.{u, w, v}) :
    GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} :=
  GreendlingerLeaf.P10Rose.regionMoveSubArc_of_singleRegionMove
    (GreendlingerLeaf.P10RoseExtremalTrim.singleRegionMove_of_junction
      (roseExtremalJunction_of_filterWalk h))

#audit_axioms GroupApproximation.Full.GL03C.glFix01_regionMoveSubArc_of_filterWalk

end GroupApproximation.Full.GL03C
