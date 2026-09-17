import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger leaf over the four missing region endpoints

Lane gl-assembly-04, first module.  The lane target is the unconditional leaf
`AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed :
RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v}`, obtained by applying
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow` to the five
hypothesis-free region endpoints of residuals 01, 04, 06, 07 and 10.

## What is on disk at authoring time

A grep of `GreendlingerLeaf` for `theorem … : <residual type>` with no binders finds:

* residual 01 (`hbudget`, `OsinLemma94ClassEndLoopsBudgetInput`): `Piece01.proof`
  (`Piece01/Proof`), hypothesis-free now that `P01EmptyTwoGon/Endpoint` provides
  `P01EmptyTwoGon.proof`.  It is imported and used below.
* residual 04 (`hspan`, `OsinLemma94ClassCaseGapSpanStatement`): only `Piece04.proof`
  (`Piece04/Proof`), which cites the non-elaborating `Piece04/Residual` and must not be imported.
  The region endpoint `Piece04.Final.proof` (lane gl-p04-14) is not on disk.
* residual 06 (`hcellStep`, `CellPocketOuterPinchStepSectionDistinctBelowStatement`): no producer.
* residual 07 (`hproper`, `CellPocketWalkProperArcsBelowSectionStatement`): only `Piece07.proof`
  (`Piece07/Proof`), which cites the missing `P07LakeExclusion.proof` and must not be imported.  The
  region endpoint `Piece07Below.proof` (lane gl-p07-16) is not on disk.
* residual 10 (`hstep`, `PocketOuterPinchStepSectionStatement`): only `Piece10.proof`
  (`Piece10/Proof`), which cites the missing `P10Rose.rose` and must not be imported.  The region
  endpoint `Piece10.proof` of `P10RoseEndpoint/Proof` (lane gl-p10-04) is not on disk.

So the target is not closed here.  Following the lane rule "refuse to author against a name that does
not yet exist", the four missing region endpoints are stated as one Statement.

## The remaining gap: `RegionEndpointsStatement`

`RegionEndpointsStatement` is the conjunction of the interfaces of the four in-flight region
endpoints (residuals 04, 06, 07, 10).

* **True.**  Each conjunct is a section form of Osin's Lemmas 9.4 and 9.7(b)
  (arXiv:math/0411039v3, §9), and the carto truth checks of the region lanes mark each one TRUE.
* **Strictly smaller in proof content.**  The open-residual bundle of the waist,
  `AsmWaist.GreendlingerOpenResidualsBelowStatement`, has five conjuncts.  This Statement drops
  residual 01, which is discharged here by the hypothesis-free `Piece01.proof`, so it is not a
  restatement of the waist's hypothesis.  `openResidualsBelow_of_regionEndpoints` proves the bundle
  from it.

Endpoints of this module:

* `relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_fourRegionEndpoints`: the leaf from the four
  region endpoints as separate binders, in waist order `hspan, hcellStep, hproper, hstep`;
* `relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_regionEndpoints`: the leaf from the bundle.

## The unconditional endpoint, once the region endpoints land

```
theorem relativeGreendlingerQuasiGeodesicLeastAreaClosed :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_fourRegionEndpoints
    Piece04.Final.proof <P06 Below cell step endpoint> Piece07Below.proof Piece10.proof
#audit_closed_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed
```

That module must import `Piece04/Final` (or its successor), the P06 endpoint module,
`Piece07Below/Proof` and `P10RoseEndpoint/Proof`.  It must never import `GreendlingerLeaf/Assembly`,
`Piece04/Proof`, `Piece07/Proof` or `Piece10/Proof`, because `P10RoseEndpoint/Proof` redeclares
`Piece10.proof`.  `AsmClose/LiveFrontier` reduces this Statement further, to the live leaves of the
four region chains.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose

universe u w v

/-- **The four in-flight region endpoints of the Below Greendlinger waist**: residual 04 (gap span),
residual 06 (Below cell step), residual 07 (proper arcs Below) and residual 10 (outer pinch step).
This is the remaining gap of lane gl-assembly-04.  Residual 01 is supplied by `Piece01.proof`. -/
def RegionEndpointsStatement : Prop :=
  OsinLemma94ClassCaseGapSpanStatement.{u, w, v} ∧
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} ∧
      CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} ∧
        PocketOuterPinchStepSectionStatement.{u, w, v}

/-- **The open residuals of the Below waist from the four region endpoints**: residual 01 is the
hypothesis-free `Piece01.proof`. -/
theorem openResidualsBelow_of_regionEndpoints (h : RegionEndpointsStatement.{u, w, v}) :
    AsmWaist.GreendlingerOpenResidualsBelowStatement.{u, w, v} :=
  ⟨Piece01.proof.{u, w, v}, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **Osin's Lemma 4.4 at least-area diagrams from the four in-flight region endpoints**, given as
separate binders.  Residual 01 is `Piece01.proof`, and residuals 05, 08, 09 are the closed trio of
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow`. -/
theorem relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_fourRegionEndpoints
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow
    Piece01.proof.{u, w, v} hspan hcellStep hproper hstep

/-- **Osin's Lemma 4.4 at least-area diagrams from the bundled region endpoints.** -/
theorem relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_regionEndpoints
    (h : RegionEndpointsStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_fourRegionEndpoints h.1 h.2.1 h.2.2.1
    h.2.2.2

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.RegionEndpointsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.openResidualsBelow_of_regionEndpoints
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_fourRegionEndpoints
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_regionEndpoints
