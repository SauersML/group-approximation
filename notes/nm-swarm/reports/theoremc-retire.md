# theoremc-retire lane report

Lane `theoremc-retire` (clone cs-stages) of the non-MF every-line swarm.
Updated 2026-09-13.

## Status

First target closed. Root-imported `Manuscript/NonMF/TheoremCAssembly.lean` has no
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

Second item closed: W3 hT6, with kh-cckw.
- kh-cckw has reduced hT6 to hzip and hfold.
- This lane has landed the matching flip of Theorem C (e1b326ec3).

Current item: W1, one second-level piece of `OsinLemma94PlanarRunInput`, with
hull-unbound. This lane proposed Case 2 (bridge exchange). hull-unbound assigns the
piece and its interface. See the W1 section below.

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |
| b1dc27674 | attic copy of the zip-and-fold flip of `TheoremCAssemblyKOLeaves` (before the probe) |
| e1b326ec3 | normal landing of that flip after green probe `0913-021752-29195` (base b1dc27674) |
| 84241b175, 3e9636d74 | this report and the census row (after 2c3c8cb40 and after e1b326ec3) |
| aa7391c47 | report correction: `SystolicDiscZipPinch` landed unverified in d74b84054 |

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

## W3 hT6 (with kh-cckw)

kh-cckw landed the whole fixed-clique assembly in 7d64d1118:
- `GGT/SystolicInvariantClique.lean`: `dist_iso`,
  `exists_invariantClique_of_graphConditions` and
  `exists_invariantClique_of_linksSixLarge`.
- `Kazhdan/CCKWSystolicInvariantClique.lean`:
  - `CCKW.systolicInvariantClique_of_zipFold (hzip : ∀ V X, ZipSpurStatement X)
    (hfold : ∀ V X, MirrorFoldStatement X) : SystolicInvariantCliqueStatement`;
  - `KMSGroup.sharpExistence_ghb7_of_zipFoldHyp`, which takes `hzip` and `hfold`
    at `CCKW.cosetComplex`, plus `IsHyperbolicGroup (GHB 7)`.

So hT6 is no longer an independent leaf. With
`GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold`, `hKO` follows from `hzip` and
`hfold` at the coset complex alone.

Flip (this lane, e1b326ec3): `TheoremCAssemblyKOLeaves` adds
`manuscriptTorsionFreeFullMFRadical_of_leastAreaZipFold` and
`manuscriptTorsionFreeSimplified_of_leastAreaZipFold`. They take four hypotheses:
`hgreendlinger`, `hbridge`, `hzip` and `hfold`. Probe `0913-021752-29195` built
the module, and all four `#audit_axioms` lines passed.

Below `hzip` and `hfold`, main already reduces each one to disc cases:
- `Systolic.zipSpurStatement_of_zipPinch` (`GGT/SystolicDiscZip.lean:61`);
- `Systolic.mirrorFoldStatement_of_cases` (`GGT/SystolicDiscMirrorFoldCases.lean:113`).

On origin (checked at e1b326ec3), none of the three case Props has a producer,
but all three are in progress:
- `Systolic.ZipPinchStatement X` (`GGT/SystolicDiscZipFold.lean:281`):
  systolic-counts. Its `GGT/SystolicDiscZipPinch.lean`, which states
  `theorem zipPinchStatement (X) : ZipPinchStatement X`, landed unverified in
  d74b84054. Its probe is running.
- `Systolic.MirrorFoldPinchedStatement X` (`GGT/SystolicDiscMirrorFoldCases.lean:102`):
  fff-periodic. Its staging layer `GGT/SystolicDiscMirrorFoldStage.lean` landed in
  d6f6ccc19.
- `Systolic.MirrorFoldDistinctStatement X` (`GGT/SystolicDiscMirrorFoldCases.lean:93`):
  ko-closed, under Offer B in its report. ko-closed's `SystolicDiscMirrorFoldCases`
  probe is green, and there is no Distinct module yet.

My earlier proposal to take `MirrorFoldPinchedStatement` is withdrawn, because
fff-periodic has started it.

## W1 h94 planar half (with hull-unbound)

hull-unbound split h94 in b8441172e (`Estimating/OsinLemma94Pieces.lean`) into
`OsinLemma94AntiparallelMetricStatement` (hull-count94) and
`OsinLemma94PlanarRunInput` (hull-unbound). The second-level pieces of the planar half:
- (P) the component polygons, after
  `GloballyDistinguishedSectionFamily.exists_unselectedGFacesReduced`
  (`Estimating/OsinUnboundReduced.lean`, sec5-sentences);
- (C1) Case 1: a backwards pair whose target is an (A1) or (A2) side contradicts
  `weight_maximal`, through `RealizedSectionFamily.false_of_quadrilateral_region`
  (`Estimating/OsinUnboundCaseOne.lean`, on main);
- (C2) Case 2: a backwards pair whose target lies on a cutting path contradicts the
  minimality of `∑ l(t_j)`, by exchanging the path segment for a connector.

This lane proposed C2 to hull-unbound and asked for the interface before building.

Finding for C2. Osin's second minimality has no carrier yet.
`GloballyDistinguishedSectionFamily` (`Estimating/OsinAppendixSections.lean:265`) has
`label_admissible`, `weight_maximal` and `card_minimal`, and `SectionCuts` has no path
data. A path-limited git grep of `GGT/VanKampen` on origin/main finds "cutting path"
only in docstrings. So C2 comes with the measure that (P) minimizes, and the two pieces
share that interface. After both reductions an unselected component is one G-face,
and its cutting paths are the edges with that face on both sides. One candidate measure
is the dart count of the diagram among reduced globally distinguished families. The
reductions keep `family.card` and the unbound sum, and an exchange removes a segment
longer than `ε` and inserts a connector shorter than `ε`. This is a proposal to
hull-unbound, not a decision.

## Residual Props (exact)

- `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
  (hgreendlinger; hull-respell)
- `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`
  (hbridge; hull-bridge)
- `TheoremC.KotowskiOllivierStatement` (hKO; ko-closed). In the
  `_of_leastAreaZipFold` forms of `TheoremCAssemblyKOLeaves` it is replaced by:
  - `Systolic.ZipSpurStatement KMSGroup.CCKW.cosetComplex` (hzip; kh-torsion),
    which reduces to `Systolic.ZipPinchStatement`;
  - `Systolic.MirrorFoldStatement KMSGroup.CCKW.cosetComplex` (hfold;
    fff-periodic and ko-closed), which reduces to
    `Systolic.MirrorFoldDistinctStatement` and
    `Systolic.MirrorFoldPinchedStatement`.
- hT6 (`KMSGroup.CCKW.SystolicInvariantCliqueStatement`) follows from `hzip`
  and `hfold` for every X (`systolicInvariantClique_of_zipFold`).

## Census

`metadata/nm-census-rows/theoremc-retire.tsv` has one row: LINE:284, `partial`.
Its carriers are the `_of_leastAreaInputs`, `_of_leastAreaKOLeaves` and
`_of_leastAreaZipFold` endpoints. Its note retires the baseline finding
"root-imported TheoremCAssembly has 5 sorries" (census2 U2). The LINE:284 row in
`sec5-sentences` names the printed-theorem carriers; this row only adds to it.

## Stale references outside this lane's files (for the lead; sweep on hold)

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

- W1: build the piece hull-unbound assigns, most likely C2 in a new
  `Estimating/OsinUnboundCaseTwo.lean`. Send the statement to hull-unbound first, then
  land it unverified, probe, and land it normally.
- All three disc cases under hzip and hfold are started by other lanes, so this lane
  has claimed none.
- One-application flips, owned by this lane:
  - once hzip and hfold land closed at `CCKW.cosetComplex`, the
    `_of_leastAreaZipFold` forms lose both binders;
  - once ko-closed lands `kotowskiOllivier_closed` and the lead wires
    `Kazhdan.KotowskiOllivierClosed`, `hKO` goes from the `_of_leastAreaInputs`
    forms and from `SeedFromTheoremC`;
  - hgreendlinger and hbridge go the same way as they close.
