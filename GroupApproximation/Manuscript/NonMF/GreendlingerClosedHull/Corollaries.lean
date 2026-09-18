import GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.Theorem
import GroupApproximation.Manuscript.NonMF.HullCorollary73
import GroupApproximation.Manuscript.NonMF.HullCorollary74
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Corollaries 7.3 and 7.4 over the five open residuals of the Greendlinger waist

Lane gl-assembly-05, second module.  `non_mf_groups_exist.tex`, lines 2166–2169 (census
`LINE:1682` in the older numbering of `metadata/nm-census-rows/cite-hull.tsv`):

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

The cited result is Hull's Corollary 7.4 (arXiv:1308.4345, §7), stated verbatim as
`HullCorollary74.PrintedHullCorollary74`.  Hull's proof of 7.4 applies his Corollary 7.3,
`HullCorollary73.PrintedHullCorollary73`.

## Route

Each theorem below applies the matching `_of_greendlinger` theorem (`HullCorollary73.lean:440`,
`HullCorollary74.lean:305`) to `GreendlingerClosedHull.leastAreaLeaf_of_openResidualsBelow`.  The
planned hypothesis-free leaf `AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`
(lane gl-assembly-04) is not on disk, so the five open residuals
`AsmWaist.GreendlingerOpenResidualsBelowStatement.{0,0,0}` remain the one binder.  That binder is
strictly smaller in proof content than the existing binder `hgreendlinger`; see the docstring of
`GreendlingerClosedHull/Theorem`.

## Manuscript status

Every theorem here still takes `hopen`, so none of them closes a sentence on its own.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull

/-- **Hull, Corollary 7.3**, verbatim, over the five open residuals of the Below Greendlinger
waist. -/
theorem manuscriptSentence_hullCorollary73_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    HullCorollary73.PrintedHullCorollary73 :=
  HullCorollary73.printedHullCorollary73_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.manuscriptSentence_hullCorollary73_of_openResidualsBelow

/-- **Hull, Corollary 7.4**, verbatim (cited at tex line 2167), over the five open residuals of
the Below Greendlinger waist. -/
theorem manuscriptSentence_hullCorollary74_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    HullCorollary74.PrintedHullCorollary74 :=
  HullCorollary74.printedHullCorollary74_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.manuscriptSentence_hullCorollary74_of_openResidualsBelow

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull
