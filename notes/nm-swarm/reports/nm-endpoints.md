# nm-endpoints lane report

Lane `nm-endpoints`, target census2 U7: the closed top endpoints of `sec:torsion-free`
(`thm:torsion-free`, `cor:regular-nonmf-algebra`, the Fournier-Facio paragraph,
`TheoremC.LiteratureInputs`, `lem:saturation`, `thm:hull`, `TheoremC.Configuration`).

## Landed

- `12e1d1af8`: `GroupApproximation/Manuscript/NonMF/TorsionFreeFourLeaves.lean`. It was
  probed green (probe 0913-013032-80446, the bytes on main), and the `#audit_axioms` line
  of each theorem shows only `propext`, `Classical.choice` and `Quot.sound`. It is now
  root-imported (GroupApproximation.lean:4834). The module has 19 theorems
  `*_of_fourLeaves`, each over exactly the walls its proof uses.
  - Greendlinger and bridge walls only:
    - `thm:hull` at Hull's notion, at Osin's notion, at the limit-set notion, and at a
      torsion-free ambient group;
    - `lem:saturation` at the same three notions (the limit-set form uses the closed
      `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`);
    - `TheoremC.HullCommonQuotientStatement` and `TheoremC.FournierFacioQuotientStatement`.
  - Those two walls plus Kotowski-Ollivier: `TheoremC.LiteratureInputs` and
    `Nonempty TheoremC.Configuration`.
  - All four walls:
    - `TorsionFreePrinted.FournierFacioParagraph`;
    - `PrintedTorsionFreeTheorem`, plus its radical, Osin and limit-set forms;
    - `PrintedRegularNonMFAlgebra`, plus its Osin and limit-set forms.
- `de1ccf8b3` and `5f94c76f9`: docstring-only fixes; no statement changed. Both modules cited
  `thm:hull` at tex lines 1624–1628, and both now cite 1636–1642:
  - `TorsionFreeLimitSetNotion`, two docstrings (reported by sec5-sentences); probe
    0913-020633-75804 green;
  - `TorsionFreeHullPrintedLeastArea`, the module docstring; probe 0913-021058-94913 green.
- `96ebd17c2`: the TorsionFreeKOLeaves decision (section below).
- `fe61152ed`: docstring-only updates to `TorsionFreeLeafAssembly`,
  `TorsionFreeLiteratureInputsLeastArea` and `TorsionFreeSaturationFromCorrected` (reported
  by sec2-sentences), probe 0913-030945-26927 green for all three. They named
  `TheoremCAssembly` declarations that 2c3c8cb40 deleted: `hullOneStep`, `hullTheorem71`,
  `literatureInputs` and the estimating admissions. They now name
  `HullSC.hullOneStepStatement_of_leastAreaLeaves`,
  `TorsionFree.hullTheorem71_of_leastAreaLeaves` and the surviving
  `GGT.VanKampen.Estimating*Statement`s.

## Residual statements (exact)

1. `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. On main
   its producers still take `OsinLemma97SectionStatement`
   (`relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97`) or pocket inputs.
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`. Its
   producer still takes `QuotientPeripheralLetterPullbackStatement`
   (`relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`).
3. `TheoremC.KotowskiOllivierStatement`, which is `Hyperbolic.SharpExistence`. After hzip
   closed, the fixed-clique leaf is no longer needed, and the only open leaf is
   `Systolic.MirrorFoldStatement CCKW.cosetComplex`:
   - `KMSGroup.sharpExistence_ghb7_of_zipFoldHyp hzip hfold hhyp`
     (Kazhdan/CCKWSystolicInvariantClique.lean:68) concludes `Hyperbolic.SharpExistence`;
   - `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold hzip hfold`
     (Kazhdan/GHBHyperbolicDiscCounts.lean:84) gives `hhyp`;
   - `CCKW.zipSpur_cosetComplex` (GGT/SystolicDiscZip.lean:131, 8389a0e6c) gives `hzip`. It
     carries `#audit_closed_axioms` and is root-imported (GroupApproximation.lean:4755).
4. CLOSED: `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`. It is proved by
   `HydeLodha.finitelyPresentedInfiniteSimple_closed`
   (GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleClosed.lean:49, 47b31bef8), which
   carries `#audit_closed_axioms` and is root-imported (GroupApproximation.lean:4790).
   Every `hW` binder below is spent by that one application.

Every other input is already closed: DGO 2.35, GO 1.1, Chiodo, Minasyan–Osin, the
free-product union geometry, and the hard direction of Osin 1.1.

## Flip plan

When closed producers of a set of walls land, each endpoint needing only those walls
becomes
`theorem printedFoo : PrintedFoo := TorsionFreeFourLeaves.printedFoo_of_fourLeaves <walls>`,
followed by `#audit_closed_axioms`.

- Walls 1 and 2: `thm:hull`, `lem:saturation`, `HullCommonQuotientStatement`,
  `FournierFacioQuotientStatement`.
- Walls 1 to 3: `LiteratureInputs` and `Configuration` (row dab2f2bfe084). Once hfold closes,
  `hKO` is
  `KMSGroup.sharpExistence_ghb7_of_zipFoldHyp CCKW.zipSpur_cosetComplex hfold
  (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold CCKW.zipSpur_cosetComplex hfold)`.
- All four walls: `FournierFacioParagraph`, `thm:torsion-free`, `cor:regular-nonmf-algebra`.
  Wall 4 is closed, so these wait on walls 1 to 3 only. The flip passes
  `HydeLodha.finitelyPresentedInfiniteSimple_closed` as `hW`. This lane lands no three-leaf
  wrapper, since reshaping a binder retires no finding.

## Census rows

`metadata/nm-census-rows/nm-endpoints.tsv` is keyed by sentence hash. Every row is
`partial` and names its exact residual walls. The rows are:
- a16637da7249: the torsion-free clause of the abstract;
- 0f22bdbc4184: thm:torsion-free;
- dce7a9ff4e83: the sentence at tex 293;
- 7b1fa3182135 and 8b1ec28a0e73: cor:regular-nonmf-algebra;
- 4895f03fdf5f and 8aead549f1fe: thm:hull;
- 2f55113239ce: lem:saturation;
- 8097c371f35d: the Fournier-Facio sentence;
- dab2f2bfe084: the G_0 sentence.

None of them retires a baseline finding: a four-leaf form reshapes a conditional, it does
not discharge one. No row was added for the proof-step rows bcc99703f838, 2d1cd22e5f49,
2f997e5af4e6 and 721da4c14d11, because no four-leaf theorem proves those sentences exactly.

## Wall status on main (checked 2026-09-13 at origin f495cf119)

- Wall 4 is closed (above).
- Wall 3: hzip is closed (above). The open leaf is hfold, and its remaining cases are
  `MirrorFoldDistinctStatement` and `MirrorFoldPinchedStatement`. dgo-geometric's truth
  audit found both true for every triangle complex. theoremc-retire's
  `TheoremCAssemblyFoldLeaf` (f019265bb) states Theorem C over hgreendlinger, hbridge and
  hfold at every triangle complex. The root does not import it.
- Walls 1 and 2 have no closed producer. No closed producer of
  `OsinLemma97SectionStatement` or `QuotientPeripheralLetterPullbackStatement` has landed.
  The W1 pocket carrier is dgo-analytic's `PocketRegion`
  (Estimating/OsinPocketRegion.lean:68, 497542415).
- `TheoremCAssembly` has no `sorry` left (2c3c8cb40). `kotowskiOllivier` there became the
  hypothesis `hKO`.

## Flip readiness (checked at origin/main)

Each producer's conclusion is exactly the binder of the four-leaf theorems, so a flip is one
line:
- `relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97` concludes
  `RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v}`;
- `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback` concludes
  `.{u, v, w}`;
- `KMSGroup.sharpExistence_ghb7_of_zipFoldHyp` concludes `Hyperbolic.SharpExistence`, the
  body of `Manuscript.NonMF.TheoremC.KotowskiOllivierStatement`;
- `HydeLodha.finitelyPresentedInfiniteSimple_closed` concludes the unique
  `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`
  (FournierFacioParagraphFromSimpleFactor.lean:353).

Two orphan modules from 3cf9bd845 close no wall and do not collide with the
`TorsionFreeFourLeaves` names:
- `Kazhdan/KotowskiOllivierLeaves` (ko-closed's) has `kotowskiOllivierStatement_of_leaves` and
  the `*_of_leastAreaKOLeaves` forms, over the zip, fold and fixed-clique leaves;
- `Manuscript/NonMF/TorsionFreeKOLeaves` (this lane's; decision below) has the
  `*_of_leastAreaFixedCliqueHyp` and `*_of_hullFixedCliqueHyp` forms, over the fixed-clique
  leaf and the hyperbolicity of `GHB(7)`.

`#audit_axioms` throws on any axiom outside the classical allowlist
(Meta/AxiomGuard.lean), so the green probe shows that no four-leaf chain uses `sorryAx`.

## TorsionFreeKOLeaves: unwired orphan, no deletion (agreed with the lead)

- Leave `Manuscript/NonMF/TorsionFreeKOLeaves.lean` unchanged on main (blob 4c6a119ae). Do not
  probe it and do not queue it for wiring.
- Each of its seven forms is the matching `TorsionFreeFourLeaves.*_of_fourLeaves` form with
  `hKO := KMSGroup.sharpExistence_ghb7_of_fixedCliqueHyp hT6 hhyp`
  (Kazhdan/GHBSharpExistenceSystolic.lean:47). The flip never needs it, and wiring it would
  add seven open-predicate findings to the baseline and retire none.
- Its two `cor:regular-nonmf-algebra` forms still take `hDGO` and `hGO`, but both citations are
  already proved: `TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed` and
  `TorsionFreePrinted.gerasimovaOsinTheorem11Printed`.

## Open-predicate findings over the least-area leaves (classification)

Only the four walls block these findings. Each retires when the walls close: the row names
the closed endpoint and says "retires open-predicate <decl>".
- Census note names Greendlinger and bridge walls (baseline lines 214–289):
  - `TorsionFreeLeastAreaAssembly.manuscriptTorsionFreeTheorem_of_leastAreaLeaves`,
    `manuscriptRegularNonMFAlgebra_of_leastAreaLeaves`,
    `printedSaturationNoOmega_of_leastAreaLeaves`;
  - `TorsionFreeOsinNotion.manuscriptTorsionFreeTheoremOsin_of_leastAreaLeaves`,
    `manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves`,
    `manuscriptSaturationOsin_of_leastAreaLeaves`;
  - `TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves`,
    `manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves`;
  - `TorsionFreeLimitSetEndpoints.manuscriptHullTheoremLimitSet_of_leastAreaLeaves`,
    `manuscriptSaturationLimitSet_of_leastAreaLeaves`;
  - `GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves`;
  - `TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`. Its binders
    also include the Kotowski-Ollivier wall, which the census note does not name.
- Census note names the Hyde–Lodha wall; the routes consume all four walls (baseline lines
  220–307):
  - `TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves`,
    `manuscriptTorsionFreeTheoremOsin_of_hullLeaves`, `manuscriptRegularNonMFAlgebra_of_hullLeaves`,
    `manuscriptRegularNonMFAlgebraOsin_of_hullLeaves`, `fournierFacioParagraph_of_leastAreaLeaves`;
  - `TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO`, plus its
    Osin and limit-set forms.
- Not this lane (ROSTER):
  - sec5-sentences owns the proof-step carriers
    `TorsionFreeHullParagraphGeneral.*_of_leastAreaLeaves` (row bcc99703f838) and
    `TorsionFreeSectionSentencesLeastArea.*_of_leastAreaLeaves` (rows 2d1cd22e5f49,
    2f997e5af4e6, 721da4c14d11), with their own four-leaf forms;
  - hull-respell, hull-bridge and sec5-sentences own `GGT.RelHyp.osin24HullStep_of_boundedLeaves`.

## Next

- Watch main for closed wall producers and flip. A closed `LiteratureInputs` needs its own
  namespace, because `TheoremC.literatureInputs` was the name of the deleted admission.
- The Greendlinger and bridge walls unlock thm:hull, lem:saturation, the quotient field and
  common quotient, and their 12 findings above.
- Row f2bf6328169e (tex 1725, the DGO and GO sentence) belongs to cite-osin, which grades it
  formalized. census2 U3 lists it as a stale re-grade. It is not this lane's row.
- This lane has no closed theorem to land until a wall closes. The one-line flips stay here
  as the walls close.
- W1 assignment (lead, 2026-09-13): `OsinDescentStepInput`
  (Estimating/OsinAppendixAssemblyDescent.lean:94), or a piece of dgo-analytic's pocket core.
  - StepInput is off the live route:
    - dgo-analytic's Finding 3 says its producer is circular;
    - audit-sec5 found that its binders carry no `OsinCCondition` and no induction hypothesis;
    - the live route is `OsinSection97PocketInputsStatement` through
      `descentInput_of_sectionPocketCut`;
    - nothing outside OsinAppendixAssemblyDescent consumes StepInput.
  - audit-sec5 recommended retiring it to the lead. This lane builds nothing on it.
  - The pocket pieces (a)–(c) were split at ~04:05 among dgo-analytic, kh-ejz, kh-torsion,
    hull-respell, hull-select and go-lemma42, on `PocketRegion`.
  - This lane is waiting for the lead to reassign it. audit-sec5's candidate is the merge
    producer consumed by `GloballyDistinguishedSectionFamily.false_of_collapse_singleton`
    (Estimating/OsinAppendixCutMerge.lean:120), which has no users yet.
