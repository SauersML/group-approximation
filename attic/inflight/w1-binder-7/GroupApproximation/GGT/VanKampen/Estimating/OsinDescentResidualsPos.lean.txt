import GroupApproximation.GGT.VanKampen.Estimating.OsinDescentResiduals
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchPositive
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent of Lemma 9.7 from its residual pieces, at a positive side bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `osinDescentSection_of_residuals` and
`relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` (`Estimating/OsinDescentResiduals.lean`)
take the pinch `PocketPinchLabelledStatement`, which fails at `ε = 0`
(`OsinPocketWrapRose.pocketPinchWrapRefutation`).  The same assemblies go through with the repaired
pinch `PocketPinchLabelledPosStatement` (`Estimating/OsinPocketPinchPositive.lean`), through
`osinSectionPocketCutSection_of_residualsPos`.

* `osinDescentSection_of_residualsPos`
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos`

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.7 and
4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The descent part from the residual pieces, with the repaired pinch**: Lemma 9.4, the loop
part, the Euler count of `Φ'_M`, the multiple-edge pocket region, the face set producer, the pinch
at a positive side bound and the collar insertion. -/
theorem osinDescentSection_of_residualsPos
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinDescentSectionStatement.{u, w, v} :=
  osinDescentSection_of_pocketParts h94
    (osinMultipleEdgeCutSection_of_pieces hregion hgeodesic pocketCellTransport) hloop hcount
    (osinSectionPocketCutSection_of_residualsPos hfaces hpinch hgeodesic)

/-- **Osin's Lemma 4.4 at least-area diagrams from the residual pieces, with the repaired pinch**,
through `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts h94
    (osinMultipleEdgeCutSection_of_pieces hregion hgeodesic pocketCellTransport) hloop hcount
    (osinSectionPocketCutSection_of_residualsPos hfaces hpinch hgeodesic)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinDescentSection_of_residualsPos
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos
