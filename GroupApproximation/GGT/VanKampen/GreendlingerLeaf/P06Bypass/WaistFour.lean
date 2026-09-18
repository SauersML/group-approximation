import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFiveSection
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistBinderFive
import GroupApproximation.Meta.AxiomGuard

/-!
# The four-residual Below Greendlinger waist, residual 06 retired (lane gl-p06-03)

The five-residual Below waist `AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow`
has binders `hbudget, hspan, hcellStep, hproper, hstep`.  Residuals 06 (`hcellStep`, circular in
case (d), see `lanes/carto-gl-p06.md`) and 07 (`hproper`) enter only through binder 5 below the bound.
With the refuted walk binder (`CellPocketWalkRefutedBelowSectionStatement`, `RefutedDef.lean`),
binder 5 needs no pinch (`osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`,
`BinderFiveSection.lean`).  So residuals 06 and 07 are replaced by the single binder `hrefuted`.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow`: residual 01 (`hbudget`),
  residual 04 (`hspan`), the refuted binder (`hrefuted`) and residual 10 (`hstep`) give
  `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, through
  `Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow` (`WaistBinderFive.lean`).

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from four residuals of the Below waist**: the class
end-loop budget, the class-case gap span, the refuted cell pocket walk binder and the outer-pinch
step of the section pocket.  Residuals 06 and 07 are not used. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hrefuted : CellPocketWalkRefutedBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow hbudget hspan
    (osinMultipleEdgePocketRegionCopyBelowSection_of_refuted hrefuted) hstep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow
