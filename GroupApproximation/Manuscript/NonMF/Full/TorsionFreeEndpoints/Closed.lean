import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.Manuscript.NonMF.Full.TorsionFreeEndpoints.Reductions
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free endpoints of `non_mf_groups_exist.tex`, CONDITIONAL on Greendlinger

**CONDITIONAL, stated loudly.  Nothing in this module is unconditional.**

Lane GL07 (repair gl-fix-05).  Every theorem here takes the one explicit hypothesis

  `hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`,

the relative Greendlinger lemma at least-area diagrams (Osin, arXiv:math/0411039v3, Lemma 4.4).
**`hG` is not proved in the repository.**  So this module is a "Greendlinger ⇒ all torsion-free
endpoints" layer: it applies each `*_of_greendlinger` theorem of `TorsionFreeGreendlingerLeaf`,
`TorsionFreeGreendlingerForms`, `TorsionFreeGreendlingerSentences` and
`Full.TorsionFreeEndpoints.Reductions` to `hG`.

An earlier version of this module applied those theorems to a binder-free theorem
`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea`, and called every endpoint unconditional.
That theorem never compiled, and it is withdrawn from `Full/GL06/Assembly`, because it is not
proved.  Each endpoint that was called `X_closed` is therefore renamed `X_closed_of_greendlinger`
and takes `hG`.  No declaration of this module is used elsewhere in the repository.

## The remaining gap

`Full.GL06.relativeGreendlinger_zero_of_allCells_of_core` (`Full/GL06/Assembly`) proves `hG`
from two residual statements, both **open** (not proved in the repository):

* `Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` (binder 5, the all-cells
  disjunct of the corrected enclosed inner pocket);
* `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (residual 10, the planar kept sub-walk
  core of the rose sub-arc region move).

The last section restates the top endpoints over these two residuals
(`*_of_allCells_of_core`).  They are still CONDITIONAL.

Labels covered, all conditionally: `thm:torsion-free` with its Osin and limit-set variants,
`thm:hull`, `lem:saturation`, the Fournier-Facio paragraph, `cor:regular-nonmf-algebra`, the
proof-step sentences of `sec:torsion-free`, abstract tex 78–79, and introduction tex 292–293 and
303–305.  The statements are the conclusions of the applied theorems, unchanged; the six
parametric sentences of `TorsionFreeGreendlingerSentences` are stated at `type_of%` of the
applied theorem, so their statement is literally its conclusion.
-/

namespace GroupApproximation
namespace Full
namespace TorsionFreeEndpoints

/-! ## The bundle and the introduction and abstract sentences (from `Reductions`) -/

/-- **Every zero-parameter torsion-free endpoint, CONDITIONAL on the relative Greendlinger
lemma `hG`**, which is not proved in the repository.  `torsionFreeEndpoints_of_greendlinger`
applied to `hG`. -/
theorem torsionFreeEndpoints_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeEndpoints :=
  torsionFreeEndpoints_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_closed_of_greendlinger

/-- Abstract, tex 78–79, **CONDITIONAL on `hG`** (not proved in the repository). -/
theorem abstractTorsionFreeClause_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    AbstractTorsionFreeClause :=
  abstractTorsionFreeClause_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.abstractTorsionFreeClause_closed_of_greendlinger

/-- Introduction, tex 292–293, "The last group has none", **CONDITIONAL on `hG`** (not proved in
the repository). -/
theorem introLastGroupHasNone_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    IntroLastGroupHasNone :=
  introLastGroupHasNone_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.introLastGroupHasNone_closed_of_greendlinger

/-- Introduction, tex 303–305, **CONDITIONAL on `hG`** (not proved in the repository). -/
theorem introReducedAlgebraSentence_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    IntroReducedAlgebraSentence :=
  introReducedAlgebraSentence_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.introReducedAlgebraSentence_closed_of_greendlinger

/-! ## `TorsionFreeGreendlingerLeaf`, CONDITIONAL on `hG` -/

section Leaf

open GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf

/-- `thm:hull` as printed (tex 1636), **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger` applied to `hG`. -/
theorem leaf_printedHullTheorem_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  printedHullTheorem_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullTheorem_closed_of_greendlinger

/-- `thm:hull` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger` applied to `hG`. -/
theorem leaf_printedHullTheoremOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  printedHullTheoremOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullTheoremOsin_closed_of_greendlinger

/-- `thm:hull` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger` applied to `hG`. -/
theorem leaf_printedHullTheoremLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  printedHullTheoremLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullTheoremLimitSet_closed_of_greendlinger

/-- `thm:hull` at a torsion-free ambient group, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger`
applied to `hG`. -/
theorem leaf_hullSmallCancellationTorsionFreePrinted_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  hullSmallCancellationTorsionFreePrinted_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_hullSmallCancellationTorsionFreePrinted_closed_of_greendlinger

/-- `lem:saturation` as printed, with no finite set, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger` applied to `hG`. -/
theorem leaf_printedSaturation_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  printedSaturation_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturation_closed_of_greendlinger

/-- `lem:saturation` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger` applied to `hG`. -/
theorem leaf_printedSaturationOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedSaturationOsin :=
  printedSaturationOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationOsin_closed_of_greendlinger

/-- `lem:saturation` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger` applied to
`hG`. -/
theorem leaf_printedSaturationLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  printedSaturationLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationLimitSet_closed_of_greendlinger

/-- Hull's common quotient (Hull, Corollary 7.4, as used in the Fournier-Facio paragraph),
**CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger` applied to `hG`. -/
theorem leaf_hullCommonQuotient_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement :=
  hullCommonQuotient_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_hullCommonQuotient_closed_of_greendlinger

/-- The Fournier-Facio quotient statement, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger` applied to
`hG`. -/
theorem leaf_fournierFacioQuotient_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotient_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_fournierFacioQuotient_closed_of_greendlinger

/-- The bundle `TheoremC.LiteratureInputs`, **derived** here (it is the conclusion, not a
hypothesis), **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger` applied to `hG`. -/
theorem leaf_literatureInputs_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.LiteratureInputs :=
  literatureInputs_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_literatureInputs_closed_of_greendlinger

/-- A configuration of `TheoremC`, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.configuration_of_greendlinger` applied to `hG`. -/
theorem leaf_configuration_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Nonempty Manuscript.NonMF.TheoremC.Configuration :=
  configuration_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_configuration_closed_of_greendlinger

/-- The Fournier-Facio paragraph, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger` applied to `hG`. -/
theorem leaf_fournierFacioParagraph_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.FournierFacioParagraph :=
  fournierFacioParagraph_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_fournierFacioParagraph_closed_of_greendlinger

/-- `thm:torsion-free` as printed, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger` applied to `hG`. -/
theorem leaf_printedTorsionFreeTheorem_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  printedTorsionFreeTheorem_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeTheorem_closed_of_greendlinger

/-- `thm:torsion-free` with the full MF radical, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.printedTorsionFreeFullMFRadical_of_greendlinger`
applied to `hG`. -/
theorem leaf_printedTorsionFreeFullMFRadical_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.PrintedTorsionFreeFullMFRadical :=
  printedTorsionFreeFullMFRadical_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeFullMFRadical_closed_of_greendlinger

/-- `thm:torsion-free` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger` applied to `hG`. -/
theorem leaf_printedTorsionFreeTheoremOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  printedTorsionFreeTheoremOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeTheoremOsin_closed_of_greendlinger

/-- `thm:torsion-free` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger`
applied to `hG`. -/
theorem leaf_printedTorsionFreeTheoremLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  printedTorsionFreeTheoremLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeTheoremLimitSet_closed_of_greendlinger

/-- `cor:regular-nonmf-algebra` as printed, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebra_of_greendlinger` applied to
`hG`. -/
theorem leaf_printedRegularNonMFAlgebra_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  printedRegularNonMFAlgebra_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedRegularNonMFAlgebra_closed_of_greendlinger

/-- `cor:regular-nonmf-algebra` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraOsin_of_greendlinger`
applied to `hG`. -/
theorem leaf_printedRegularNonMFAlgebraOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  printedRegularNonMFAlgebraOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedRegularNonMFAlgebraOsin_closed_of_greendlinger

/-- `cor:regular-nonmf-algebra` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in
the repository).  `TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger`
applied to `hG`. -/
theorem leaf_printedRegularNonMFAlgebraLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  printedRegularNonMFAlgebraLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedRegularNonMFAlgebraLimitSet_closed_of_greendlinger

/-- The proof paragraph of `thm:hull`, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger` applied to `hG`. -/
theorem leaf_printedHullProofParagraph_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  printedHullProofParagraph_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullProofParagraph_closed_of_greendlinger

/-- The pair-and-Hull-again sentence of the proof of `lem:saturation`, **CONDITIONAL on `hG`**
(not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger` applied to `hG`. -/
theorem leaf_printedSaturationPairAndHullAgain_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  printedSaturationPairAndHullAgain_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationPairAndHullAgain_closed_of_greendlinger

/-- The apply-`thm:hull` sentence of the proof of `lem:saturation`, **CONDITIONAL on `hG`** (not
proved in the repository).  `TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger`
applied to `hG`. -/
theorem leaf_printedSaturationApplyHull_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  printedSaturationApplyHull_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationApplyHull_closed_of_greendlinger

/-- The apply-`lem:saturation` sentence of the proof of `thm:torsion-free`, **CONDITIONAL on
`hG`** (not proved in the repository).
`TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger` applied to `hG`. -/
theorem leaf_printedTheoremApplySaturation_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation :=
  printedTheoremApplySaturation_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTheoremApplySaturation_closed_of_greendlinger

end Leaf

/-! ## `TorsionFreeGreendlingerForms`, CONDITIONAL on `hG` -/

section Forms

open GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms

/-- The Fournier-Facio quotient statement, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger`
applied to `hG`. -/
theorem forms_fournierFacioQuotientStatement_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_fournierFacioQuotientStatement_closed_of_greendlinger

/-- Hull's common quotient, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.hullCommonQuotient_of_greendlinger` applied to `hG`. -/
theorem forms_hullCommonQuotient_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement :=
  hullCommonQuotient_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_hullCommonQuotient_closed_of_greendlinger

/-- The bundle `TheoremC.LiteratureInputs`, **derived** here (it is the conclusion, not a
hypothesis), **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.literatureInputs_of_greendlinger` applied to `hG`. -/
theorem forms_literatureInputs_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.LiteratureInputs :=
  literatureInputs_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_literatureInputs_closed_of_greendlinger

/-- The Fournier-Facio paragraph, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.fournierFacioParagraph_of_greendlinger` applied to `hG`. -/
theorem forms_fournierFacioParagraph_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.FournierFacioParagraph :=
  fournierFacioParagraph_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_fournierFacioParagraph_closed_of_greendlinger

/-- `thm:hull` as printed, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger` applied to `hG`. -/
theorem forms_manuscriptSentence_hullTheorem_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  manuscriptSentence_hullTheorem_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSentence_hullTheorem_closed_of_greendlinger

/-- `thm:hull` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger` applied to
`hG`. -/
theorem forms_manuscriptSentence_hullTheoremOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  manuscriptSentence_hullTheoremOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSentence_hullTheoremOsin_closed_of_greendlinger

/-- `thm:hull` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger` applied to `hG`. -/
theorem forms_manuscriptHullTheoremLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  manuscriptHullTheoremLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptHullTheoremLimitSet_closed_of_greendlinger

/-- `thm:hull` at a torsion-free ambient group, **CONDITIONAL on `hG`** (not proved in the
repository).
`TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger` applied
to `hG`. -/
theorem forms_hullSmallCancellationTorsionFreePrinted_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  hullSmallCancellationTorsionFreePrinted_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_hullSmallCancellationTorsionFreePrinted_closed_of_greendlinger

/-- `lem:saturation` as printed, with no finite set, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerForms.printedSaturationNoOmega_of_greendlinger` applied to
`hG`. -/
theorem forms_printedSaturationNoOmega_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  printedSaturationNoOmega_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_printedSaturationNoOmega_closed_of_greendlinger

/-- `lem:saturation` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.manuscriptSaturationOsin_of_greendlinger` applied to `hG`. -/
theorem forms_manuscriptSaturationOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedSaturationOsin :=
  manuscriptSaturationOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSaturationOsin_closed_of_greendlinger

/-- `lem:saturation` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger` applied
to `hG`. -/
theorem forms_manuscriptSaturationLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  manuscriptSaturationLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSaturationLimitSet_closed_of_greendlinger

/-- `thm:torsion-free` as printed, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheorem_of_greendlinger` applied to `hG`. -/
theorem forms_manuscriptTorsionFreeTheorem_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptTorsionFreeTheorem_closed_of_greendlinger

/-- `thm:torsion-free` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the repository).
`TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremOsin_of_greendlinger` applied to
`hG`. -/
theorem forms_manuscriptTorsionFreeTheoremOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  manuscriptTorsionFreeTheoremOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptTorsionFreeTheoremOsin_closed_of_greendlinger

/-- `thm:torsion-free` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremLimitSet_of_greendlinger`
applied to `hG`. -/
theorem forms_manuscriptTorsionFreeTheoremLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  manuscriptTorsionFreeTheoremLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptTorsionFreeTheoremLimitSet_closed_of_greendlinger

/-- `cor:regular-nonmf-algebra` as printed, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebra_of_greendlinger`
applied to `hG`. -/
theorem forms_manuscriptRegularNonMFAlgebra_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptRegularNonMFAlgebra_closed_of_greendlinger

/-- `cor:regular-nonmf-algebra` at Osin's notion, **CONDITIONAL on `hG`** (not proved in the
repository).  `TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraOsin_of_greendlinger`
applied to `hG`. -/
theorem forms_manuscriptRegularNonMFAlgebraOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  manuscriptRegularNonMFAlgebraOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptRegularNonMFAlgebraOsin_closed_of_greendlinger

/-- `cor:regular-nonmf-algebra` at the limit-set notion, **CONDITIONAL on `hG`** (not proved in
the repository).
`TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger` applied to
`hG`. -/
theorem forms_manuscriptRegularNonMFAlgebraLimitSet_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptRegularNonMFAlgebraLimitSet_closed_of_greendlinger

end Forms

/-! ## `TorsionFreeGreendlingerSentences`, CONDITIONAL on `hG`

Six of these theorems carry further binders or a long `∀`-statement.  Each is stated at
`type_of%` of the applied theorem at `hG`, so its statement is literally that conclusion. -/

section Sentences

open GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences

/-- "Hull's proof treats `m = 1` by passing to `G/⟨⟨r⟩⟩`" (tex 1644), **CONDITIONAL on `hG`**
(not proved in the repository). -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    type_of% (@manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger hG) :=
  @manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullOneTargetOneRelatorGeneral_closed_of_greendlinger

/-- "and the general case by induction on `m`" (tex 1644), **CONDITIONAL on `hG`** (not proved in
the repository). -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    type_of% (@manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger hG) :=
  @manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullInductionOnTargetsGeneral_closed_of_greendlinger

/-- `thm:hull` at Osin's notion over a torsion-free ambient group (tex 1636), **CONDITIONAL on
`hG`** (not proved in the repository). -/
theorem manuscriptSentence_hullTheoremTorsionFreeOsin_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    type_of% (@manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger hG) :=
  @manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullTheoremTorsionFreeOsin_closed_of_greendlinger

/-- The pair-and-Hull-again sentence of the proof of `lem:saturation` (tex 1662), **CONDITIONAL
on `hG`** (not proved in the repository). -/
theorem manuscriptSentence_saturationPairAndHullAgain_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    type_of% (@manuscriptSentence_saturationPairAndHullAgain_of_greendlinger hG) :=
  @manuscriptSentence_saturationPairAndHullAgain_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_saturationPairAndHullAgain_closed_of_greendlinger

/-- The apply-`thm:hull` sentence of the proof of `lem:saturation` (tex 1665), **CONDITIONAL on
`hG`** (not proved in the repository). -/
theorem manuscriptSentence_saturationApplyHullNoOmega_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    type_of% (@manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger hG) :=
  @manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_saturationApplyHullNoOmega_closed_of_greendlinger

/-- The apply-`lem:saturation` sentence of the proof of `thm:torsion-free` (tex 1698),
**CONDITIONAL on `hG`** (not proved in the repository). -/
theorem manuscriptSentence_theoremApplySaturationNoOmega_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    type_of% (@manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger hG) :=
  @manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_theoremApplySaturationNoOmega_closed_of_greendlinger

/-- Hull's common quotient as cited in the Fournier-Facio paragraph (tex 1680–1683),
**CONDITIONAL on `hG`** (not proved in the repository). -/
theorem manuscriptSentence_hullCommonQuotient_closed_of_greendlinger
    (hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.HullCommonQuotientPrinted :=
  manuscriptSentence_hullCommonQuotient_of_greendlinger hG

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullCommonQuotient_closed_of_greendlinger

end Sentences

/-! ## The top endpoints over the two open residuals

Each theorem below takes the two residuals `hall` and `hcore`, **neither proved in the
repository**, and feeds `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore`
to the `hG`-endpoint above.  They are still CONDITIONAL. -/

/-- **Every zero-parameter torsion-free endpoint, CONDITIONAL on the two open residuals** `hall`
(binder 5) and `hcore` (residual 10), neither proved in the repository. -/
theorem torsionFreeEndpoints_of_allCells_of_core
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hcore : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    TorsionFreeEndpoints :=
  torsionFreeEndpoints_closed_of_greendlinger
    (GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore)

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_allCells_of_core

/-- Abstract, tex 78–79, **CONDITIONAL on the two open residuals** `hall` and `hcore`, neither
proved in the repository. -/
theorem abstractTorsionFreeClause_of_allCells_of_core
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hcore : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    AbstractTorsionFreeClause :=
  abstractTorsionFreeClause_closed_of_greendlinger
    (GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore)

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.abstractTorsionFreeClause_of_allCells_of_core

/-- `thm:torsion-free` as printed, **CONDITIONAL on the two open residuals** `hall` and `hcore`,
neither proved in the repository. -/
theorem printedTorsionFreeTheorem_of_allCells_of_core
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hcore : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    Manuscript.NonMF.TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  leaf_printedTorsionFreeTheorem_closed_of_greendlinger
    (GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore)

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.printedTorsionFreeTheorem_of_allCells_of_core

end TorsionFreeEndpoints
end Full
end GroupApproximation

