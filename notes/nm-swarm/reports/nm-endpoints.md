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

## Next

- Watch main for closed wall producers and flip. A closed `LiteratureInputs` needs its own
  namespace, because `TheoremC.literatureInputs` in TheoremCAssembly.lean is the sorry form.
