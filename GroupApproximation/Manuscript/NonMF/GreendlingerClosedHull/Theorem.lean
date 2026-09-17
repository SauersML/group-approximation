import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull` over the five open residuals of the Greendlinger waist

Lane gl-assembly-05.  `non_mf_groups_exist.tex`, lines 2121–2126 (census line 2122; line 1636 in
older numberings), `\label{thm:hull}`:

> Let $G$ be acylindrically hyperbolic, let $N\le G$ be suitable with respect to $A$, and let
> $g_1,\dots,g_m\in G$.  Then there is a surjective homomorphism $\varphi\colon G\to Q$ such that
> $Q$ is acylindrically hyperbolic, $\varphi(g_i)\in\varphi(N)$ for all $i$, and every element of
> finite order in $Q$ is the image of an element of the same order in $G$.

## Planned route and why it is not available yet

The lane was planned to apply each `TorsionFreeGreendlingerLeaf.*_of_greendlinger` theorem to the
hypothesis-free leaf `GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`
(lane gl-assembly-04).  That theorem is not on disk: the region endpoints for residuals 01, 04,
06, 07 and 10 of the Below waist are still in flight.

The interface consumed here is already on disk as a Statement:
`GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement` (lane
gl-assembly-02), the conjunction of the five open residuals, with its reduction
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow`.  The closed trio
(residuals 05, 08, 09) is already discharged inside that reduction.  Following the author brief,
this lane imports that Statement and does not restate it.

## Why this is progress and not a restatement

The existing carriers take the whole leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`
(Osin's Lemma 4.4 at least-area diagrams) as a hypothesis.  The carriers below take only the five
open residuals.  The proof content of the eight-binder Below waist and of the three closed
residuals is supplied, so the remaining hypothesis is strictly smaller in proof content.  It is
true: each residual is a section form of Osin's Lemmas 9.4 and 9.7(b) (see
`lanes/carto-gl-assembly.md`, section 2).

Once lane gl-assembly-04 lands, each carrier closes as
`manuscriptSentence_<name>_of_openResidualsBelow ⟨hbudget, hspan, hcellStep, hproper, hstep⟩`, or
directly as `TorsionFreeGreendlingerLeaf.<name>_of_greendlinger AsmClose...Closed.{0,0,0}`.

## Manuscript status

Every theorem here still takes `hopen`, so none of them closes the sentence on its own.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull

/-- **Osin's Lemma 4.4 at least-area diagrams, at universes `.{0,0,0}`, from the five open
residuals of the Below waist.**  The closed trio is supplied by `AsmWaist.closedTrio`. -/
theorem leastAreaLeaf_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow.{0, 0, 0}
    hopen

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.leastAreaLeaf_of_openResidualsBelow

/-- **`thm:hull` as printed, at Hull's Cayley-graph notion** (tex lines 2121–2126), over the five
open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheorem_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.manuscriptSentence_hullTheorem_of_openResidualsBelow

/-- **`thm:hull` at Osin's notion** (tex lines 2121–2126), over the five open residuals of the
Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheoremOsin_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.manuscriptSentence_hullTheoremOsin_of_openResidualsBelow

/-- **`thm:hull` at the limit-set notion** (tex lines 2121–2126), over the five open residuals of
the Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheoremLimitSet_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.manuscriptSentence_hullTheoremLimitSet_of_openResidualsBelow

/-- **`thm:hull` at a torsion-free ambient group**, the case the proof of `lem:saturation` applies
(tex lines 2150–2155), over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullSmallCancellationTorsionFree_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull.manuscriptSentence_hullSmallCancellationTorsionFree_of_openResidualsBelow

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedHull
