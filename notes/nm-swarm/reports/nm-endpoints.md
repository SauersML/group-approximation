# nm-endpoints lane report

Lane `nm-endpoints`, target census2 U7: the closed top endpoints of `sec:torsion-free`
(`thm:torsion-free`, `cor:regular-nonmf-algebra`, the Fournier-Facio paragraph,
`TheoremC.LiteratureInputs`, `lem:saturation`, `thm:hull`, `TheoremC.Configuration`).

## Landed

- `12e1d1af8`: `GroupApproximation/Manuscript/NonMF/TorsionFreeFourLeaves.lean`. It was
  probed green (probe 0913-013032-80446, the bytes on main), and the `#audit_axioms` line
  of each theorem shows only `propext`, `Classical.choice` and `Quot.sound`. It is queued
  for wiring. The module has 19 theorems
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

## Residual statements (exact)

1. `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. On main
   its producers still take `OsinLemma97SectionStatement`
   (`relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97`) or pocket inputs.
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`. Its
   producer still takes `QuotientPeripheralLetterPullbackStatement`
   (`relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`).
3. `TheoremC.KotowskiOllivierStatement`, which is `Hyperbolic.SharpExistence`. Its producer
   `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_leaves` (c5a8ae8fb) still takes the
   zip, fold and fixed-clique leaves of GHB(7).
4. `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`. Its producer
   `HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_leaves` still takes
   `StabKFinitelyPresented qTwo` (Hyde–Lodha, Proposition 4.7).

Every other input is already closed: DGO 2.35, GO 1.1, Chiodo, Minasyan–Osin, the
free-product union geometry, and the hard direction of Osin 1.1.

## Flip plan

When closed producers of a set of walls land, each endpoint needing only those walls
becomes
`theorem printedFoo : PrintedFoo := TorsionFreeFourLeaves.printedFoo_of_fourLeaves <walls>`,
followed by `#audit_closed_axioms`.

- Walls 1 and 2: `thm:hull`, `lem:saturation`, `HullCommonQuotientStatement`,
  `FournierFacioQuotientStatement`.
- Walls 1 to 3: `LiteratureInputs` and `Configuration` (row dab2f2bfe084).
- All four walls: `FournierFacioParagraph`, `thm:torsion-free`, `cor:regular-nonmf-algebra`.

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

## Wall status on main (checked 2026-09-13 01:40)

- No closed producer of any of the four walls, or of their feeders
  (`OsinLemma97SectionStatement`, `QuotientPeripheralLetterPullbackStatement`,
  `UpsilonFinitelyPresented`, `StabKFinitelyPresented`).
- `TheoremC.kotowskiOllivier` (TheoremCAssembly.lean:653) is still `sorry`.
- The fff-quotient lane has Proposition 4.7 green over exactly Lemma 4.6
  (`UpsilonFinitelyPresented`).

## Flip readiness (checked at origin/main)

Each producer's conclusion is exactly the binder of the four-leaf theorems, so a flip is one
line:
- `relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97` concludes
  `RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v}`;
- `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback` concludes
  `.{u, v, w}`;
- `KotowskiOllivierClosed.kotowskiOllivier_of_leaves` concludes
  `Manuscript.NonMF.TheoremC.KotowskiOllivierStatement`;
- `HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_leaves` concludes the unique
  `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`
  (FournierFacioParagraphFromSimpleFactor.lean:353).

`#audit_axioms` throws on any axiom outside the classical allowlist
(Meta/AxiomGuard.lean), so the green probe shows that no four-leaf chain uses `sorryAx`.

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
  namespace, because `TheoremC.literatureInputs` in TheoremCAssembly.lean is the sorry form.
- The Greendlinger and bridge walls unlock thm:hull, lem:saturation, the quotient field and
  common quotient, and their 12 findings above.
