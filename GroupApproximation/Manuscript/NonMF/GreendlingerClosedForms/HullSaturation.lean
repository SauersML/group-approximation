import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms
import GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.Leaf
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull` and `lem:saturation` forms over the five open residuals

Lane gl-assembly-09.  `non_mf_groups_exist.tex`:

* census line 2122 (1636 in older numberings), `\label{thm:hull}`:
  > Let $G$ be acylindrically hyperbolic, let $N\le G$ be suitable with respect to $A$, and let
  > $g_1,\dots,g_m\in G$.  Then there is a surjective homomorphism $\varphi\colon G\to Q$ such that
  > $Q$ is acylindrically hyperbolic, $\varphi(g_i)\in\varphi(N)$ for all $i$, and every element of
  > finite order in $Q$ is the image of an element of the same order in $G$.
* census line 2136 (1650 in older numberings), `\label{lem:saturation}`:
  > Let $G$ be finitely presented, torsion-free, and acylindrically hyperbolic, and let
  > $N\trianglelefteq G$ be nontrivial.  Then there is a surjective homomorphism
  > $\varphi\colon G\to Q$ such that $Q$ is two-generated, finitely presented, torsion-free, and
  > acylindrically hyperbolic, and $\varphi(N)=Q$.

Each theorem applies the matching `TorsionFreeGreendlingerForms.*_of_greendlinger`
(`TorsionFreeGreendlingerForms.lean:93-154`) to `leastAreaLeaf_of_openResidualsBelow`.  The
remaining hypothesis `hopen` is explained in `GreendlingerClosedForms/Leaf`.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms

/-! ## `thm:hull` -/

/-- **`thm:hull` as printed, at every acylindrically hyperbolic group** (`\label{thm:hull}`), over
the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheoremForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_hullTheoremForm_of_openResidualsBelow

/-- **`thm:hull` as printed, at Osin's notion** (`\label{thm:hull}`), over the five open residuals
of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheoremOsinForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_hullTheoremOsinForm_of_openResidualsBelow

/-- **`thm:hull` at the limit-set notion** (`\label{thm:hull}`), over the five open residuals of
the Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheoremLimitSetForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_hullTheoremLimitSetForm_of_openResidualsBelow

/-- **`thm:hull` at a torsion-free ambient group** (`\label{thm:hull}`), over the five open
residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullSmallCancellationTorsionFreePrintedForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_hullSmallCancellationTorsionFreePrintedForm_of_openResidualsBelow

/-! ## `lem:saturation` -/

/-- **`lem:saturation` as printed** (`\label{lem:saturation}`), over the five open residuals of the
Below Greendlinger waist. -/
theorem manuscriptSentence_printedSaturationNoOmegaForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerForms.printedSaturationNoOmega_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_printedSaturationNoOmegaForm_of_openResidualsBelow

/-- **`lem:saturation` at Osin's notion** (`\label{lem:saturation}`), over the five open residuals
of the Below Greendlinger waist. -/
theorem manuscriptSentence_saturationOsinForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerForms.manuscriptSaturationOsin_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_saturationOsinForm_of_openResidualsBelow

/-- **`lem:saturation` at the limit-set notion** (`\label{lem:saturation}`), over the five open
residuals of the Below Greendlinger waist.  The hard direction of Osin's Theorem 1.1 is applied as
a theorem inside the form. -/
theorem manuscriptSentence_saturationLimitSetForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_saturationLimitSetForm_of_openResidualsBelow

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms
