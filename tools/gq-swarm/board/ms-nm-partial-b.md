# ms-nm-partial-b
Direction: close the last 11 `partial` rows of metadata/NON_MF_SENTENCE_CENSUS.tsv (census rows 674 675 676 677 679 680 683 684 690 696 697; tex thm:hull, lem:saturation, Fournier-Facio paragraph, thm:torsion-free proof, cor:regular-nonmf-algebra).
- 09-18 ~14:45 CDT: all 11 rows ride ONE open Prop, the W1 waist `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` (hgreendlinger). Bridge, Kotowski-Ollivier, Hyde-Lodha, DGO 2.35, Gerasimova-Osin 1.1 are closed and applied (per NON_MF_SENTENCE_MAP notes).
- The waist is being discharged by the other session's GL/NM lanes (NMWire2.Census lists the residual alternatives). Respecting the 2 h rule; looking for an alternative no lane touched recently.

## Result (09-18 ~14:55 CDT): no row closable without W1; nothing landed
Every one of the 11 rows has exactly one open hypothesis, hG = `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`
(Osin 4.4 at least-area diagrams, inside Hull Thm 7.1). All other inputs are closed on main and applied: bridge, Kotowski–Ollivier, Hyde–Lodha,
DGO 2.35, Gerasimova–Osin 1.1 (`TorsionFreeAlgebraSentencesClosed`, parametric in Q), Hull 5.7/5.8 (`printedHullLemma58`), Hull 3.5 (`printedHullLemma35`).
Current reduction: hG ⇐ `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore`, where
  hall  = `Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` (binder 5; GL06h3–h8 descent chain, latest residual `GL06h8.gl06h8_classPocketStatement`)
  hcore = `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (residual 10; ⇔ `GL03DKeptProof.gl03dKeptProof_PinchCoreStatement`, "Jordan content")
and there are alternatives in `Full/NMWire2/Census` (residual 10 via `P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement`; binder 5 Route B).
All are in the other session's GL/P10 lanes (last commits 16:14–18:36Z, P10 still hot). The bundle `TorsionFreeEndpoints.torsionFreeEndpoints_of_allCells_of_core`
already carries all 11 rows over {hall, hcore}, so a per-row restatement would be a reshape, not a discharge (not done). ms-nm-uncond-b owns the build check of `TorsionFreeEndpoints/Closed`.

Row → carrier (all in `GroupApproximation.Full.TorsionFreeEndpoints`, Closed.lean, each `(hG) → printed Prop`):
- 674, 675 thm:hull: `leaf_printedHullTheorem_closed_of_greendlinger` (+ `…Osin…`, `…LimitSet…`, `leaf_hullSmallCancellationTorsionFreePrinted_…`, `forms_manuscriptSentence_hullTheorem_…`)
- 676 Hull's proof paragraph: `leaf_printedHullProofParagraph_…`, `manuscriptSentence_hullOneTargetOneRelatorGeneral_…`, `manuscriptSentence_hullInductionOnTargetsGeneral_…`
- 677 lem:saturation: `leaf_printedSaturation_…` (+ Osin, LimitSet), `forms_printedSaturationNoOmega_…`
- 679 Hull 5.7/5.8 pair + "Hull again": `leaf_printedSaturationPairAndHullAgain_…`, `manuscriptSentence_saturationPairAndHullAgain_…` (the pair itself closed)
- 680 apply thm:hull to N_0: `leaf_printedSaturationApplyHull_…`, `manuscriptSentence_saturationApplyHullNoOmega_…`
- 683 Fournier-Facio construction: `leaf_fournierFacioParagraph_…`, `leaf_fournierFacioQuotient_…`, `leaf_literatureInputs_…`, `leaf_configuration_…`, `forms_fournierFacioParagraph_…`
- 684 G_0 via Hull Cor 7.4: `leaf_hullCommonQuotient_…`, `forms_hullCommonQuotient_…`, `manuscriptSentence_hullCommonQuotient_…`
- 690 apply lem:saturation to G_0, N: `leaf_printedTheoremApplySaturation_…`, `manuscriptSentence_theoremApplySaturationNoOmega_…`
- 696, 697 cor:regular-nonmf-algebra: `leaf_printedRegularNonMFAlgebra_…` (+ Osin, LimitSet), `forms_manuscriptRegularNonMFAlgebra_…`
Flip condition: all 11 rows become formalized by one application once hall and hcore (or a census alternative) get closed producers.
Status: idle. Rows remaining: all 11.
