import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOff
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-16: the enclosed inner pocket from the lake-walk reading

This file composes lane gl-p07-16's reduction `pocketFourPieceOff_of_lakeRead` with lane gl-p07-15's
`innerPocketEnclosed_of_fourPieceOff`.  The result is
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (Osin, arXiv:math/0411039v3, §9,
Lemma 9.7(b)), with `PocketFourPieceLakeReadStatement` as the only remaining input.

Once a proof `pocketFourPieceLakeRead : PocketFourPieceLakeReadStatement` exists, the endpoints
close unconditionally:
* `pocketFourPieceOff := pocketFourPieceOff_of_lakeRead pocketFourPieceLakeRead`;
* `innerPocketEnclosed := innerPocketEnclosed_of_lakeRead pocketFourPieceLakeRead`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The enclosed inner pocket from the lake-walk four-piece reading.** -/
theorem innerPocketEnclosed_of_lakeRead (h : PocketFourPieceLakeReadStatement.{u, w, v}) :
    P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} :=
  innerPocketEnclosed_of_fourPieceOff (pocketFourPieceOff_of_lakeRead h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.innerPocketEnclosed_of_lakeRead

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
