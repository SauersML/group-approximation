# theoremc-retire lane report

Lane `theoremc-retire` (clone cs-stages) of the non-MF every-line swarm.
Updated 2026-09-13.

## Status

Target closed. Root-imported `Manuscript/NonMF/TheoremCAssembly.lean` has no
`sorry`. The six `sorry` tokens left in the four modules below are docstring
prose.

Probe `0913-013843-30184` (base a6e97fbd2) built and compiled all four modules
with no errors:
- `Manuscript.NonMF.TheoremCAssembly`
- `Manuscript.MFRecognition.SeedFromTheoremC`
- `Manuscript.MFRecognition.SeedRemarkTheoremC`
- `Manuscript.NonMF.TheoremCAssemblyKOLeaves`

Every `#audit_axioms` and `#audit_closed_axioms` line in them throws on any axiom
outside `propext`, `Classical.choice` and `Quot.sound`, so all of them passed.

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |

## What changed

Deleted from `TheoremCAssembly` (no file was deleted):
- the four unconsumed sorry declarations `estimatingSelectionConstruction`,
  `estimatingUnboundOutput`, `relativeIsoperimetricBridgeQuasiGeodesic` and
  `hullRelatorRespelling`;
- the chain that consumed them: `hullLemma44FamilyInclusionJoint`,
  `hullLemma44FamilyInclusion`, `hullLemma44Canonical`,
  `hullLemma49GeodesicPowerDiagram`, `hullLemma49KernelPower`,
  `hullCanonicalQuotient`, `hullOneStep`, `hullTheorem71` and `hullInputs`;
- the `kotowskiOllivier` sorry, together with `smallCancellationQuotient`,
  `hullCommonQuotient` and `literatureInputs`;
- `manuscriptTorsionFreeFullMFRadical_openAdmissions` and
  `manuscriptTorsionFreeSimplified_openAdmissions`.

The statements these declarations inhabited stay in the library.
`HullSC.HullRelatorRespellingStatement` is not proved: the roster calls it too
strong as printed.

Added:
- `TorsionFree.hullTheorem71_of_leastAreaLeaves` and
  `TorsionFree.hullInputs_of_leastAreaLeaves` build Hull's bundle from
  `hgreendlinger` and `hbridge`, through
  `HullSC.hullOneStepStatement_of_leastAreaLeaves`.
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs :
  PrintedTorsionFreeFullMFRadical` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaInputs :
  PrintedTorsionFreeSimplified`. Both take `hgreendlinger`, `hbridge` and
  `hKO`, through
  `TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`.
  There is no simple-group binder.
- `#audit_closed_axioms` lines on `dgoTheorem53` and
  `relativeExteriorArcConversionAtWord`.
- `TheoremCAssemblyKOLeaves` adds
  `manuscriptTorsionFreeFullMFRadical_of_leastAreaKOLeaves` and
  `manuscriptTorsionFreeSimplified_of_leastAreaKOLeaves`. They take
  `hgreendlinger`, `hbridge`, `hzip`, `hfold` and `hT6`, through
  `KotowskiOllivierClosed.kotowskiOllivier_of_leaves`. The module is unwired
  because `Kazhdan.KotowskiOllivierClosed` is unwired.
- `MFRecognition.SeedFromTheoremC.E` is now chosen from
  `manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs`. Every declaration
  there, and `Switch.seedCodeC_not_isOperatorMF`, takes the three hypotheses
  as explicit arguments.

Rule 22. The importers of `TheoremCAssembly` are:
- the root;
- `SeedFromTheoremC`, imported only by `SeedRemarkTheoremC`, which only the
  root imports;
- `TheoremCAssemblyKOLeaves`;
- `scripts/TheoremCCompletionAudit.lean`.

Every Lean module on that list went into the probe; the script is not a
module.

## Residual Props (exact)

- `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
  (hgreendlinger; hull-respell)
- `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`
  (hbridge; hull-bridge)
- `TheoremC.KotowskiOllivierStatement` (hKO; ko-closed). In
  `TheoremCAssemblyKOLeaves` it is replaced by:
  - `Systolic.ZipSpurStatement KMSGroup.CCKW.cosetComplex` (hzip; kh-torsion)
  - `Systolic.MirrorFoldStatement KMSGroup.CCKW.cosetComplex` (hfold; fff-periodic)
  - `KMSGroup.CCKW.SystolicInvariantCliqueStatement` (hT6; census2 U1)

## Census

`metadata/nm-census-rows/theoremc-retire.tsv` has one row: LINE:284, `partial`.
Its carriers are the four endpoints above. Its note retires the baseline finding
"root-imported TheoremCAssembly has 5 sorries" (census2 U2). The LINE:284 row in
`sec5-sentences` names the printed-theorem carriers; this row only adds to it.

## Stale references outside this lane's files (for the lead)

These Lean docstrings name deleted `TheoremCAssembly` declarations or its "five
admissions" (whole-word check on origin/main). The code hits for
`kotowskiOllivier`, `smallCancellationQuotient` and `hullCommonQuotient` are
`LiteratureInputs` fields, and those are fine.
- `GGT/HullSCCommonQuotientCorrected.lean:202`
- `GGT/HullSCLemma44Canonical.lean:289`
- `GGT/HullSCLemma44JointRelabel.lean:680-684`
- `GGT/HullSCLemma49PowerDiagramFromComponents.lean:8`
- `GGT/HullSCOneStepQuasiGeodesicLeaves.lean:25-38`
- `Kazhdan/GHBLatticeRouteKazhdan.lean:68`
- `Kazhdan/KotowskiOllivierClosed.lean:12`
- `Manuscript/NonMF/FFFParagraphFreeWitness.lean:60-68, 304-318`
- `Manuscript/NonMF/FournierFacioParagraphFromSimpleFactor.lean:94-114, 474`
- `Manuscript/NonMF/HullFillTheoremCCorrected.lean:19`
- `Manuscript/NonMF/TorsionFreeLeafAssembly.lean:36-37, 123`
- `Manuscript/NonMF/TorsionFreeLiteratureInputsLeastArea.lean:18-23, 101`
- `Manuscript/NonMF/TorsionFreeSaturationFromCorrected.lean:21, 74, 264, 435`
- `Manuscript/NonMF/TorsionFreeSectionCitations.lean:38-43, 167`: the table still
  says two fields report `sorryAx`.

Other stale references:
- `scripts/TheoremCCompletionAudit.lean` audits declarations that no longer
  exist. No lake root and no CI job uses it, so nothing breaks, but it cannot
  pass as written.
- The note of row c6172bdc109a in `metadata/MF_RECOGNITION_SENTENCE_MAP.tsv`
  says E is chosen from `TorsionFree.manuscriptTorsionFreeFullMFRadical_closed`.
  E is chosen from `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs`.
  The `partial` grade stays right.
- The "REMOVED 2026-09-07" comment block in
  `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` says `TheoremCAssembly.lean`
  inherited four `sorry`s.
- The swarm rules header still says TheoremCAssembly has 5 sorries.
- hull-respell's "if any consumer remains" item: nothing supplies
  `HullSC.HullRelatorRespellingStatement` any more. It remains as the binder
  `hrespell` at `GGT/HullSCLemma44FamilyAssembly.lean:548, 655, 670`,
  `GGT/HullSCLemma44QuasiGeodesicBridge.lean:412, 476` and
  `GGT/HullSCLemma44RespellingBinders.lean:229`.

## Next

- When ko-closed lands `kotowskiOllivier_closed` and the lead wires
  `Kazhdan.KotowskiOllivierClosed`, drop `hKO` from the `_of_leastAreaInputs`
  forms and from `SeedFromTheoremC` with one application. Do the same for
  hgreendlinger and hbridge as they close.
- The roster scope is finished; waiting for the next item from the lead.
