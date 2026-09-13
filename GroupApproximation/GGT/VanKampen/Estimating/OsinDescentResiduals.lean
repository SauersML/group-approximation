import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCutResiduals
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerPocketParts
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent of Lemma 9.7 from its residual pieces

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `osinDescentSection_of_pocketParts`
(`OsinAppendixGreendlingerPocketParts`) takes Lemma 9.4, the two cut parts and the two
producers.  Two of them come from pocket pieces:
* the multiple-edge part, `osinMultipleEdgeCutSection_of_pieces`
  (`OsinPocketMultipleEdgeAssembly`), from `OsinMultipleEdgePocketRegionSectionStatement` (lane
  `kh-ejz`);
* the section pocket producer, `osinSectionPocketCutSection_of_residuals`
  (`OsinPocketCutResiduals`), from the face set producer (lane `kh-ejz`) and the pinch (lane
  `hull-respell`).

Both use the cell transport, which is go-lemma42's `pocketCellTransport`, and the collar
insertion `GeodesicCollarStatement` (lane `kh-torsion`), which is passed once here.

* `osinDescentSection_of_residuals`
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-- **The descent part from the residual pieces**: Lemma 9.4, the loop part, the Euler count of
`Φ'_M`, the multiple-edge pocket region, the face set producer, the pinch and the collar
insertion. -/
theorem osinDescentSection_of_residuals
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinDescentSectionStatement.{u, w, v} :=
  osinDescentSection_of_pocketParts h94
    (osinMultipleEdgeCutSection_of_pieces hregion hgeodesic pocketCellTransport) hloop hcount
    (osinSectionPocketCutSection_of_residuals hfaces hpinch hgeodesic)

/-- **Osin's Lemma 4.4 at least-area diagrams from the residual pieces**: the Greendlinger waist,
through `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts h94
    (osinMultipleEdgeCutSection_of_pieces hregion hgeodesic pocketCellTransport) hloop hcount
    (osinSectionPocketCutSection_of_residuals hfaces hpinch hgeodesic)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinDescentSection_of_residuals
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
