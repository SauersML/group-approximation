# theoremc-retire lane report

Lane `theoremc-retire` (clone cs-stages) of the non-MF every-line swarm.
Updated 2026-09-13.

## Status

- First item closed. Root-imported `Manuscript/NonMF/TheoremCAssembly.lean` has no
  `sorry` (2c3c8cb40, probe `0913-013843-30184`).
- Second item closed: W3 hT6 with kh-cckw, which gave the zip-and-fold flip of
  Theorem C (e1b326ec3).
- Third item closed: Theorem C without hzip, in `TheoremCAssemblyFoldLeaf`
  (f019265bb, probe `0913-034425-9721`).
- Fourth item closed: the roster flip of `TheoremCAssemblyFoldLeaf`. hbridge and
  hfold are both closed, so `TheoremCAssemblyGreendlingerLeaf` (c5f953323, probe
  `0913-060950-64731`) states Theorem C over hgreendlinger alone.
- Next item: C1 of `OsinLemma94PlanarRunInput`. sec5-sentences holds Case 2. This
  lane is waiting for hull-unbound's realization interface.

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |
| b1dc27674 | attic copy of the zip-and-fold flip of `TheoremCAssemblyKOLeaves` (before the probe) |
| e1b326ec3 | normal landing of that flip after green probe `0913-021752-29195` (base b1dc27674) |
| 84241b175, 3e9636d74, aa7391c47, a0607c71f | this report and the census row |
| f019265bb | new `Manuscript/NonMF/TheoremCAssemblyFoldLeaf.lean` (before the probe). Probe `0913-034425-9721` (base 5f9c16b7b) compiled these exact bytes (md5 a2db324a), so there was no second landing |
| c5f953323 | new `Manuscript/NonMF/TheoremCAssemblyGreendlingerLeaf.lean` (before the probe). Probe `0913-060950-64731` (base 5f789a7ba) compiled these exact bytes (md5 7dea5861), so there was no second landing |

## Theorem C without hzip, and over hgreendlinger alone

`TheoremCAssemblyFoldLeaf` (f019265bb, green):
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaFold` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaFold` take `hgreendlinger`,
  `hbridge` and `hfold : ∀ (V : Type) (X : Systolic.TriangleComplex V),
  Systolic.MirrorFoldStatement X`.
- They apply the `_of_leastAreaZipFold` forms of `TheoremCAssemblyKOLeaves` at
  `hzip := KMSGroup.CCKW.zipSpur_cosetComplex` (8389a0e6c), with hfold used at
  `CCKW.cosetComplex`.
- The `hfold` binder has the shape `CCKW.systolicInvariantClique_of_zipFold`
  consumes. It is stronger than the `CCKW.cosetComplex` hypothesis of the
  `_ZipFold` forms, so those forms remain the sharper statements.
- Imports: `TheoremCAssemblyKOLeaves`, `GGT.SystolicDiscZip` and
  `Meta.AxiomGuard`, all root-reachable on origin. So there is no wiring
  dependency. `Kazhdan.KotowskiOllivierClosed` and `TheoremCAssemblyKOLeaves`
  are root-imported (`GroupApproximation.lean:4824` and `4831`).
- Wire-queue line added.

`TheoremCAssemblyGreendlingerLeaf` (c5f953323, green):
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_greendlinger` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_greendlinger` take `hgreendlinger`
  alone. Both `#audit_axioms` lines passed.
- They apply the `_of_leastAreaFold` forms at
  `hbridge := HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
  (hull-bridge, 18682110d) and `hfold := fun _ X => Systolic.mirrorFold X`
  (fff-periodic, 426813b24).
- Wire-queue line added. Wire it after `TheoremCAssemblyFoldLeaf`,
  `GGT.HullSCLemma51EmbeddedBridgeHolds` and `GGT.SystolicDiscMirrorFold`, all
  three queued.

## What changed in the first item

Deleted from `TheoremCAssembly` (no file was deleted):
- the four unconsumed sorry declarations `estimatingSelectionConstruction`,
  `estimatingUnboundOutput`, `relativeIsoperimetricBridgeQuasiGeodesic` and
  `hullRelatorRespelling`, and the chain that consumed them;
- the `kotowskiOllivier` sorry, with `smallCancellationQuotient`,
  `hullCommonQuotient` and `literatureInputs`;
- both `_openAdmissions` endpoints.

Added:
- `TorsionFree.hullTheorem71_of_leastAreaLeaves` and
  `TorsionFree.hullInputs_of_leastAreaLeaves`.
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaInputs`, over
  `hgreendlinger`, `hbridge` and `hKO`, with no simple-group binder.
- `TheoremCAssemblyKOLeaves`: the `_of_leastAreaKOLeaves` forms (hzip, hfold, hT6)
  and, after W3, the `_of_leastAreaZipFold` forms (hzip, hfold).
- `MFRecognition.SeedFromTheoremC.E` is chosen from
  `manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and takes the three
  hypotheses explicitly.

Rule 22: every Lean importer of `TheoremCAssembly` went into the probe.
`scripts/TheoremCCompletionAudit.lean` is not a module.

## W3 hT6 (with kh-cckw)

kh-cckw's `CCKW.systolicInvariantClique_of_zipFold` (7d64d1118) reduces hT6 to hzip and
hfold. `KMSGroup.sharpExistence_ghb7_of_zipFoldHyp` with
`GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold` gives hKO from hzip and hfold at the
coset complex. All disc cases below them are now closed on origin:
- hzip: `KMSGroup.CCKW.zipSpur_cosetComplex` (8389a0e6c);
- hfold: `Systolic.mirrorFold` (426813b24), from ko-closed's `mirrorFoldDistinct`
  (81b06b43e) and fff-periodic's `mirrorFoldPinched`.

## W1 h94 planar half

hull-unbound split h94 in b8441172e (`Estimating/OsinLemma94Pieces.lean`) into
`OsinLemma94AntiparallelMetricStatement` and `OsinLemma94PlanarRunInput`. The planar
half has three second-level pieces:
- (P) the component polygons, realized on the face walks of a reduced family
  (hull-unbound);
- (C1) a backwards pair whose target is an (A1) or (A2) side contradicts
  `weight_maximal`, through `RealizedSectionFamily.false_of_quadrilateral_region`
  (`Estimating/OsinUnboundCaseOne.lean`). **This lane.**
- (C2) a backwards pair whose target lies on a cutting path contradicts the
  minimality of the cut, by exchanging the path segment for a connector
  (sec5-sentences, with the dart-count measure this lane proposed; modules
  `SurgerySpikeDeletion*` and `Estimating/OsinUnboundBridgeExchange`).

Finding for C1. `OsinLemma94PlanarPolygons` carries corners and side words only.
`longSides` is `N1 ∪ N2` and does not separate cutting paths from (A2) arcs. So C1
cannot be stated over the structure's fields alone. It needs, for the target side,
the G-face of `S.diagram` and the traversal `X ++ T ++ Y ++ P` that
`false_of_quadrilateral_region` consumes. This lane asked hull-unbound for its
realization interface. Failing that, it proposes to state C1 in a new
`Estimating/OsinUnboundCaseOneRun.lean` over an explicit realization hypothesis.

## Residual Props (exact)

- `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
  (hgreendlinger; hull-respell and W1). It is the only binder of the
  `_of_greendlinger` forms of Theorem C.
- Closed walls: hbridge (`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`),
  hzip, hfold, and hT6 (which follows from hzip and hfold).
- `TheoremC.KotowskiOllivierStatement` (hKO). `kotowskiOllivier_of_pinched` needs
  only Pinched, so `kotowskiOllivier_closed` is one application (ko-closed). It is
  not on origin (checked at a4b4bc783). It is still a binder of the root-imported
  `_of_leastAreaInputs` forms and of `SeedFromTheoremC`.

## Census

`metadata/nm-census-rows/theoremc-retire.tsv` has one row, LINE:284, graded
`partial`. Its carriers are the `_of_leastAreaInputs`, `_of_leastAreaKOLeaves`,
`_of_leastAreaZipFold`, `_of_leastAreaFold` and `_of_greendlinger` endpoints (10
declarations). Its note retires the baseline finding "root-imported
TheoremCAssembly has 5 sorries" (census2 U2). The grade stays `partial` while
hgreendlinger is open.

## Stale references

sec2-sentences closed the stale TheoremC docstring backlog listed in earlier
versions of this report (2e93f09d1, 12738313c, 9ac39c698, 8f8b5ccab), as the roster
records. One item remains: nothing supplies `HullSC.HullRelatorRespellingStatement`.
It is still the binder `hrespell` at `GGT/HullSCLemma44FamilyAssembly.lean:548, 655, 670`,
`GGT/HullSCLemma44QuasiGeodesicBridge.lean:412, 476` and
`GGT/HullSCLemma44RespellingBinders.lean:229`.

## Next

- C1 of `OsinLemma94PlanarRunInput`, after hull-unbound's answer. The statement
  goes to hull-unbound before any build.
- Offered to the lead: once GreendlingerLeaf is wired, re-point
  `SeedFromTheoremC.E` at `_of_greendlinger`.
- One-application flip, this lane: once hgreendlinger closes, the `_of_greendlinger`
  forms become closed Theorem C, and LINE:284 can be regraded.
