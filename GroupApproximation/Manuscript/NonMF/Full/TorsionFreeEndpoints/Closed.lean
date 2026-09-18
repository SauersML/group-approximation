import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.Manuscript.NonMF.Full.TorsionFreeEndpoints.Reductions
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free endpoints of `non_mf_groups_exist.tex`, closed

Lane GL07.  Every `*_of_greendlinger` theorem of `TorsionFreeGreendlingerLeaf`,
`TorsionFreeGreendlingerForms`, `TorsionFreeGreendlingerSentences` and
`Full.TorsionFreeEndpoints.Reductions` has exactly one binder, the relative Greendlinger lemma
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (Osin, Lemma 4.4, at
least-area diagrams).  This module applies each of them to the closed theorem `GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea` of lane
GL06, so every endpoint below is unconditional.

Labels covered: `thm:torsion-free` with its Osin and limit-set variants, `thm:hull`,
`lem:saturation`, the Fournier-Facio paragraph, `cor:regular-nonmf-algebra`, the proof-step
sentences of `sec:torsion-free`, abstract tex 78–79, and introduction tex 292–293 and 303–305.

Each `_closed` theorem is stated at `type_of%` of the corresponding reduction applied to the
GL06 theorem.  Its statement is therefore literally the reduction's conclusion.
-/

namespace GroupApproximation
namespace Full
namespace TorsionFreeEndpoints

/-- **Every zero-parameter torsion-free endpoint of `non_mf_groups_exist.tex`, unconditional.** -/
theorem torsionFreeEndpoints_closed : TorsionFreeEndpoints :=
  torsionFreeEndpoints_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_closed

/-- Abstract, tex 78–79, unconditional. -/
theorem abstractTorsionFreeClause_closed : AbstractTorsionFreeClause :=
  abstractTorsionFreeClause_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.abstractTorsionFreeClause_closed

/-- Introduction, tex 292–293, "The last group has none", unconditional. -/
theorem introLastGroupHasNone_closed : IntroLastGroupHasNone :=
  introLastGroupHasNone_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.introLastGroupHasNone_closed

/-- Introduction, tex 303–305, unconditional. -/
theorem introReducedAlgebraSentence_closed : IntroReducedAlgebraSentence :=
  introReducedAlgebraSentence_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.introReducedAlgebraSentence_closed

/-! ## `TorsionFreeGreendlingerLeaf` -/

/-- `TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedHullTheorem_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullTheorem_closed

/-- `TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedHullTheoremOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullTheoremOsin_closed

/-- `TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedHullTheoremLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullTheoremLimitSet_closed

/-- `TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_hullSmallCancellationTorsionFreePrinted_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_hullSmallCancellationTorsionFreePrinted_closed

/-- `TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedSaturation_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturation_closed

/-- `TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedSaturationOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationOsin_closed

/-- `TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedSaturationLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationLimitSet_closed

/-- `TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_hullCommonQuotient_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_hullCommonQuotient_closed

/-- `TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_fournierFacioQuotient_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_fournierFacioQuotient_closed

/-- `TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_literatureInputs_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_literatureInputs_closed

/-- `TorsionFreeGreendlingerLeaf.configuration_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_configuration_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.configuration_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.configuration_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_configuration_closed

/-- `TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_fournierFacioParagraph_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_fournierFacioParagraph_closed

/-- `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedTorsionFreeTheorem_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeTheorem_closed

/-- `TorsionFreeGreendlingerLeaf.printedTorsionFreeFullMFRadical_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedTorsionFreeFullMFRadical_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeFullMFRadical_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeFullMFRadical_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeFullMFRadical_closed

/-- `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedTorsionFreeTheoremOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeTheoremOsin_closed

/-- `TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedTorsionFreeTheoremLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTorsionFreeTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTorsionFreeTheoremLimitSet_closed

/-- `TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebra_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedRegularNonMFAlgebra_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebra_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebra_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedRegularNonMFAlgebra_closed

/-- `TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedRegularNonMFAlgebraOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedRegularNonMFAlgebraOsin_closed

/-- `TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedRegularNonMFAlgebraLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedRegularNonMFAlgebraLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedRegularNonMFAlgebraLimitSet_closed

/-- `TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedHullProofParagraph_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedHullProofParagraph_closed

/-- `TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedSaturationPairAndHullAgain_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationPairAndHullAgain_closed

/-- `TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedSaturationApplyHull_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedSaturationApplyHull_closed

/-- `TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem leaf_printedTheoremApplySaturation_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedTheoremApplySaturation_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.leaf_printedTheoremApplySaturation_closed

/-! ## `TorsionFreeGreendlingerForms` -/

/-- `TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_fournierFacioQuotientStatement_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_fournierFacioQuotientStatement_closed

/-- `TorsionFreeGreendlingerForms.hullCommonQuotient_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_hullCommonQuotient_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullCommonQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullCommonQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_hullCommonQuotient_closed

/-- `TorsionFreeGreendlingerForms.literatureInputs_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_literatureInputs_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.literatureInputs_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.literatureInputs_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_literatureInputs_closed

/-- `TorsionFreeGreendlingerForms.fournierFacioParagraph_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_fournierFacioParagraph_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioParagraph_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioParagraph_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_fournierFacioParagraph_closed

/-- `TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptSentence_hullTheorem_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSentence_hullTheorem_closed

/-- `TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptSentence_hullTheoremOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSentence_hullTheoremOsin_closed

/-- `TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptHullTheoremLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptHullTheoremLimitSet_closed

/-- `TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_hullSmallCancellationTorsionFreePrinted_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_hullSmallCancellationTorsionFreePrinted_closed

/-- `TorsionFreeGreendlingerForms.printedSaturationNoOmega_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_printedSaturationNoOmega_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.printedSaturationNoOmega_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.printedSaturationNoOmega_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_printedSaturationNoOmega_closed

/-- `TorsionFreeGreendlingerForms.manuscriptSaturationOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptSaturationOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSaturationOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSaturationOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSaturationOsin_closed

/-- `TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptSaturationLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptSaturationLimitSet_closed

/-- `TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheorem_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptTorsionFreeTheorem_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheorem_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptTorsionFreeTheorem_closed

/-- `TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptTorsionFreeTheoremOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptTorsionFreeTheoremOsin_closed

/-- `TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptTorsionFreeTheoremLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptTorsionFreeTheoremLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptTorsionFreeTheoremLimitSet_closed

/-- `TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebra_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptRegularNonMFAlgebra_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebra_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebra_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptRegularNonMFAlgebra_closed

/-- `TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptRegularNonMFAlgebraOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptRegularNonMFAlgebraOsin_closed

/-- `TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem forms_manuscriptRegularNonMFAlgebraLimitSet_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptRegularNonMFAlgebraLimitSet_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_closed_axioms GroupApproximation.Full.TorsionFreeEndpoints.forms_manuscriptRegularNonMFAlgebraLimitSet_closed

/-! ## `TorsionFreeGreendlingerSentences` (the sentences carry their own parameters) -/

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullOneTargetOneRelatorGeneral_closed

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullInductionOnTargetsGeneral_closed

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_hullTheoremTorsionFreeOsin_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullTheoremTorsionFreeOsin_closed

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_saturationPairAndHullAgain_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_saturationPairAndHullAgain_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_saturationPairAndHullAgain_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_saturationPairAndHullAgain_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_saturationPairAndHullAgain_closed

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_saturationApplyHullNoOmega_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_saturationApplyHullNoOmega_closed

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_theoremApplySaturationNoOmega_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_theoremApplySaturationNoOmega_closed

/-- `TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger`, applied to GL06's relative Greendlinger theorem. -/
theorem manuscriptSentence_hullCommonQuotient_closed : type_of% (@GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}) :=
  @GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

#audit_axioms GroupApproximation.Full.TorsionFreeEndpoints.manuscriptSentence_hullCommonQuotient_closed

end TorsionFreeEndpoints
end Full
end GroupApproximation
