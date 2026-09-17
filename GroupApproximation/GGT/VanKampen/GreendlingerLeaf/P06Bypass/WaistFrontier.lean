import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistFour
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Gaps
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.OuterPinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The bypass frontier of the Greendlinger leaf (lane gl-p06-03, second endpoint)

The tight frontier `AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier`
(`AsmFrontier/Tight.lean`) has four open Statements, one of which is the circular
`Piece06.CellRoseUncutLakesBelowStatement`.  Through the four-residual waist (`P06Bypass/WaistFour`)
that Statement drops out:

* `hbudget` by `Piece01.proof` (as in `Tight.lean`);
* `hspan` by `AsmFrontier.gapSpan_of_rotationTurns hrot`;
* `hstep` by `AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof hsub`;
* `hrefuted` by the lane gl-p06-01 reduction from the long inner two-arc Statement, or from the
  enclosed inner pocket through `P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed`.

Endpoints:

* `relativeGreendlingerQuasiGeodesicLeastArea_of_bypassTightFrontier_of_interfaces`: from `hrot`,
  `hinner : P07LakeExclusion.CellPocketInnerTwoArcLongStatement` and `hsub`;
* `relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier_of_interfaces`: the lane endpoint
  `relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier (hrot hencl hsub)`.

Both carry the two lane-interface hypotheses `hfive` (lane gl-p06-02) and `hlong` (lane gl-p06-01),
which were not on disk at authoring time.  Once they land, the lane endpoint is

```
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hencl : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow Piece01.proof.{u, w, v}
    (AsmFrontier.gapSpan_of_rotationTurns hrot)
    (P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (P06Bypass.refutedBelowSection_of_innerPocketEnclosed hencl))
    (AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof.{u, w, v} hsub)
```

Only the modules `Tight.lean` already imports (`Piece01/Proof`, `P10ChordLift/Proof`) are imported
among the region proofs; `GreendlingerLeaf/Assembly`, `Piece04/Proof`, `Piece06/Proof`,
`Piece07/Proof` and `Piece10/Proof` are not.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from the bypass tight frontier**: the rotation turns of
a class pocket, the long inner two-arc and the sub-arc region move of the rose case, with the two
lane-interface hypotheses `hfive` (gl-p06-02) and `hlong` (gl-p06-01).  No Piece06 Statement is
used. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_bypassTightFrontier_of_interfaces
    (hfive : BinderFiveOfRefutedStatement.{u, w, v})
    (hlong : RefutedOfInnerTwoArcLongStatement.{u, w, v})
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hinner : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow_of_binderFive hfive
    Piece01.proof.{u, w, v} (AsmFrontier.gapSpan_of_rotationTurns hrot) (hlong hinner)
    (AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof.{u, w, v} hsub)

/-- **Osin's Lemma 4.4 at least-area diagrams from the bypass frontier**: the rotation turns of a
class pocket, the enclosed inner pocket and the sub-arc region move of the rose case, with the two
lane-interface hypotheses `hfive` (gl-p06-02) and `hlong` (gl-p06-01).  No Piece06 Statement is
used. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier_of_interfaces
    (hfive : BinderFiveOfRefutedStatement.{u, w, v})
    (hlong : RefutedOfInnerTwoArcLongStatement.{u, w, v})
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hencl : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_bypassTightFrontier_of_interfaces hfive hlong hrot
    (P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed hencl) hsub

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassTightFrontier_of_interfaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier_of_interfaces
