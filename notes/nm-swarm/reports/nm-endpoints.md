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
- The ten census rows are re-graded at origin 6fd3d7a55 (section "Census rows").

## Residual statements (exact, at origin 6fd3d7a55)

1. OPEN: `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. On
   main its producers still take `OsinLemma97SectionStatement`
   (`relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97`) or pocket inputs. The pocket
   layer on `PocketRegion` is still landing (latest a4cd9934d).
2. CLOSED: `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`.
   - It is proved by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
     (GGT/HullSCLemma51EmbeddedBridgeHolds.lean:20, 18682110d).
   - That proof applies `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`
     to `quotientPeripheralLetterPullbackStatement_holds`
     (GGT/HullSCLemma51LetterPullbackHolds.lean:60).
   - Both carry `#audit_closed_axioms`, and both are queued for root wiring (hull-bridge).
   - Its universes `.{0, 0, 0}` match the `hbridge` binder (TorsionFreeFourLeaves.lean:70).
3. OPEN: `TheoremC.KotowskiOllivierStatement`, which is `Hyperbolic.SharpExistence`. Its only
   open leaf is `Systolic.MirrorFoldPinchedStatement CCKW.cosetComplex` (fff-periodic).
   - `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_pinched`
     (Kazhdan/KotowskiOllivierClosed.lean:59, cf1675f3b) concludes the statement from
     `hpinch` alone. It was probed green (0913-045023-55941) and is root-imported
     (GroupApproximation.lean:4824).
   - It uses `CCKW.zipSpur_cosetComplex` (GGT/SystolicDiscZip.lean:131, 8389a0e6c,
     root-imported) for the zip leaf.
   - It uses `Systolic.mirrorFoldDistinct` (GGT/SystolicDiscMirrorFoldDistinct.lean:230,
     81b06b43e) for the distinct case. That module was probed green (0913-044647-45237) and is
     queued for wiring.
   - It then passes `Systolic.mirrorFoldStatement_of_cases` to
     `sharpExistence_ghb7_of_zipFoldHyp`.
4. CLOSED: `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`.
   - It is proved by `HydeLodha.finitelyPresentedInfiniteSimple_closed`
     (GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleClosed.lean:49, 47b31bef8).
   - It carries `#audit_closed_axioms` and is root-imported (GroupApproximation.lean:4790).

Every other input is already closed: DGO 2.35, GO 1.1, Chiodo, Minasyan–Osin, the
free-product union geometry, and the hard direction of Osin 1.1.

## Flips (owned by theoremc-retire)

theoremc-retire owns the one-application flips. This lane re-grades the rows as walls close.
Each flip is
`theorem printedFoo : PrintedFoo := TorsionFreeFourLeaves.printedFoo_of_fourLeaves <walls>`,
followed by `#audit_closed_axioms`, where `<walls>` are the closed producers above.
- Walls 1 and 2, now waiting on wall 1 only: `thm:hull`, `lem:saturation`,
  `HullCommonQuotientStatement`, `FournierFacioQuotientStatement`.
- Walls 1 to 3, now waiting on wall 1 and `hpinch`: `LiteratureInputs` and `Configuration`
  (row dab2f2bfe084).
- All four walls, now waiting on wall 1 and `hpinch`: `FournierFacioParagraph`,
  `thm:torsion-free`, `cor:regular-nonmf-algebra`.
- `hKO` is `kotowskiOllivier_of_pinched hpinch`. KotowskiOllivierClosed's docstring names
  the future closed `kotowskiOllivier_closed` as that one application.
- This lane lands no reduced-leaf wrapper, since reshaping a binder retires no finding.

## Census rows

`metadata/nm-census-rows/nm-endpoints.tsv` is keyed by sentence hash.
- Every row is `partial` and names its exact residual premises and the closed ones.
- The rows are:
  - a16637da7249: the torsion-free clause of the abstract;
  - 0f22bdbc4184: thm:torsion-free;
  - dce7a9ff4e83: the sentence at tex 293;
  - 7b1fa3182135 and 8b1ec28a0e73: cor:regular-nonmf-algebra;
  - 4895f03fdf5f and 8aead549f1fe: thm:hull;
  - 2f55113239ce: lem:saturation;
  - 8097c371f35d: the Fournier-Facio sentence;
  - dab2f2bfe084: the G_0 sentence.
- None of them retires a baseline finding: a four-leaf form reshapes a conditional, it does not
  discharge one.
- No row was added for the proof-step rows bcc99703f838, 2d1cd22e5f49, 2f997e5af4e6 and
  721da4c14d11, because no four-leaf theorem proves those sentences exactly.
- The merged census unions the carriers of every lane's row on a hash:
  - 4895f03fdf5f and 8aead549f1fe also carry fff-quotient's `LINE:1636` row, the Hyde–Lodha
    `Q₂` witness for `FinitelyPresentedInfiniteSimpleStatement`. Line 1636 is the `thm:hull`
    header, so that key looks misplaced.
  - 8097c371f35d also carries hl-lemma46's row.
  - dab2f2bfe084 also carries cite-hull's row.

## Wall status on main (checked 2026-09-13 at origin 6fd3d7a55)

- Walls 2 and 4 are closed (above).
- Wall 3 waits on `MirrorFoldPinchedStatement` alone. dgo-geometric's truth audit found both
  fold cases true for every triangle complex. theoremc-retire's `TheoremCAssemblyFoldLeaf`
  (f019265bb) states Theorem C over hgreendlinger, hbridge and hfold at every triangle complex.
  The root does not import it.
- Wall 1 has no closed producer. No closed producer of `OsinLemma97SectionStatement` has
  landed.
- `HullCitationSentences.printedHullTheorem312*` and `printedSaturationHullPair`, and
  `HullTheorem312Lemma58.printedHullTheorem312`, are closed and root-imported. They carry tex
  1629–1630 and 1662 (Hull Theorem 3.12, Corollary 5.7, Lemma 5.8). They are not `thm:hull` and
  not the statement of `lem:saturation`, so no row of this lane changes.

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

These findings are blocked only by wall 1 and `hpinch`. Each retires when its flip lands: the
row names the closed endpoint and says "retires open-predicate <decl>".
- The census note names the Greendlinger and bridge walls (baseline lines 214–289):
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
- The census note names the Hyde–Lodha wall, but the routes consume all four walls (baseline
  lines 220–307):
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

- `OsinDescentStepInput` is RETIRED as off route (lead, 2026-09-13; audit-sec5 and
  dgo-analytic agree). This lane built nothing on it and deleted nothing. dgo-analytic adds the
  docstring note.
- The next build piece is the loop-cap Prop for `LoopCutInput`
  (GGT/VanKampen/Estimating/OsinAppendixSectionInduction.lean:86). It starts once audit-sec5
  reports its cap test and the lead rules on the shape. Nothing is built before that ruling.
- Meanwhile, keep the ten rows current as wall 1 and `hpinch` close.
- A closed `LiteratureInputs` needs its own namespace, because `TheoremC.literatureInputs` was
  the name of the deleted admission.
- Row f2bf6328169e (tex 1725, the DGO and GO sentence) belongs to cite-osin, which grades it
  formalized. census2 U3 lists it as a stale re-grade. It is not this lane's row.
