import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistInterface
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistBinderFive
import GroupApproximation.Meta.AxiomGuard

/-!
# The four-residual Below Greendlinger waist, residual 06 retired (lane gl-p06-03)

The five-residual Below waist `AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow`
has binders `hbudget, hspan, hcellStep, hproper, hstep`.  Residuals 06 (`hcellStep`, circular in
case (d), see `lanes/carto-gl-p06.md`) and 07 (`hproper`) enter only through binder 5 below the bound.
With the refuted walk binder, binder 5 needs no pinch (lane gl-p06-02), so residuals 06 and 07 are
replaced by the single refuted binder `hrefuted`.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow_of_binderFive`: the lane
  endpoint `relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow (hbudget hspan hrefuted
  hstep)`, with the lane gl-p06-02 theorem as the interface hypothesis `hfive`.

## When lanes gl-p06-01 and gl-p06-02 land

Their names were not on disk at authoring time.  The hypothesis-free-in-`hfive` endpoint is the
one-liner

```
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hrefuted : P06Bypass.CellPocketWalkRefutedBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow hbudget hspan
    (P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted hrefuted) hstep
```

(`Waist.CellPocketWalkRefutedBelowSectionStatement` is the lane gl-p06-01 shape verbatim, so the two
refuted Statements agree definitionally.)

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from four residuals of the Below waist**: the class
end-loop budget, the class-case gap span, the refuted cell pocket walk binder and the outer-pinch
step of the section pocket.  Residual 06 is not used.  The hypothesis `hfive` is the lane gl-p06-02
theorem (binder 5 from the refuted binder), stated as `BinderFiveOfRefutedStatement`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow_of_binderFive
    (hfive : BinderFiveOfRefutedStatement.{u, w, v})
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hrefuted : CellPocketWalkRefutedBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow hbudget hspan (hfive hrefuted) hstep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow_of_binderFive
