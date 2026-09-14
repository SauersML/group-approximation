# root-wire lane report

Lane `root-wire` (clone `lead`).  Brief: wire landed, closed modules into the root
`GroupApproximation.lean` in batched waves; drain `$NM/wire-queue.txt`; wire the census-carrier modules
of `metadata/NON_MF_SENTENCE_MAP.tsv` that the root does not reach.  Root builds only through
`nmwire.sh`; this lane never edits the root by hand.

## Pre-flight used before every wave

* `rw/rwtool.py <sha> status`: import lines precede the first `/-!`; every root import names a module
  on the sha; no duplicate root lines; no dangling import in the root closure.
* `rw/rwtool.py <sha> wave <Module...>`: for the new closure, dangling imports, lexical
  `sorry`/`admit`/`axiom`, import cycles (Tarjan over root closure plus the wave), and the tops.
* `dupcheck.py <sha> <Module...>`: declaration-name collisions between newly reachable files and the
  root closure.  Each predicted collision is read in both files; the regex also matches docstring lines
  that begin with a keyword (`theorem is ...`, `class and ...`).
* Evidence (`rw/rwgate.py`, from wave 4).  Every file of the new root closure that the previous root build
  did not compile needs a GREEN probe record.  A file was not compiled when it lies outside the closure of
  the previous build's base root plus that wave, or its bytes changed since that base; this also catches
  modules that other campaigns root by hand.  A record covers a file when the file lies in the import
  closure of the record's `# mods`, and its bytes equal the record's md5 line or, for a file outside the
  overlay, the blob at the record's base.  So a transitive build counts.  `nmprobe.sh` writes an md5 line
  for every overlay file, built or not, and failed probes write records too, so a bare md5 line proves
  nothing.  Records read: `$NM/lanes` and the fz campaign's `fz/lanes`.
* A module is held when no GREEN record newer than its last failed probe covers its bytes.
* Release by closure identity (`rw/rwclosure.py`, from wave 14).  A held module is released when three things hold:
  every file in its import closure on the sha is byte-identical to the inputs of one GREEN record (the md5
  line for an overlay file, else the blob at the record's base); `lean-toolchain` and `lake-manifest.json`
  match that record's base; and the FAILED probe's log shows no error in the module.  A module's build depends
  only on those inputs, so it builds green on the sha.  GREEN and FAILED are read from each record's `# PROBE`
  line, since `nmprobe.sh` writes a `.green.<tag>` file even when the probe fails.
* `rw/rwtool.py <sha> census`: census tokens resolved to declaring files; carriers whose files are not
  root-reachable.
* The whole queue is swept against the root closure, not only the entries added since the last wave.  The
  sweep at 00ccbca81 found two entries that the wave 3 to 6 candidate lists had missed (wave 7, below).
* `nmwire.sh` builds on the origin at launch, which can be newer than the pre-flight sha.  The next wave's
  gate diffs against that build base, so the files that changed in between are gated there.

## 09-13 root state (origin/main eb314a807, 10:56)

* Root at eb314a807 (after wave 10):
  * 4980 GroupApproximation import lines, all before the module docstring (OK);
  * no missing module and no duplicate line;
  * closure 6397 modules, with 0 dangling imports inside it;
  * 317 modules on main are not reachable from the root.  Earlier counts: 333 at 045b5f849, 310 at 5f789a7ba,
    313 at e32bac3f3, 360 at f495cf119.
* Census at eb314a807: every carrier module is root-reachable.
  * At f5873fc2a, six carrier modules were not root-reachable:
    `Estimating.OsinLemma94{ChainRespell, PolygonCount, PolygonCovers, PolygonRealization, RegionSideCount,
    SeparatingRemoval}`.  Wave 10 wired all six.
  * One census token resolves to no declaration: row 8fdc908a49c7 (definition)
    `GroupApproximation.StableWhitehead.elementaryColim_normal`.

### Root lines added by other campaigns

* 8e61df1ae (04:03, "root the GKP 4.2 endpoint") added four root lines by hand,
  `CommutingSoficActions.{DiagonalRestriction, Endpoint, FreeActionSofic, KunThomCosetAction}`, and changed
  the docstring of `Algebra.DiagonalCosetAction`.  The fz record fz-integrate 0913-034654-15072 (GREEN, base
  e12190690, `# mods` naming `Endpoint` and `DiagonalCosetAction`) carries all five files with the bytes that
  wave 4's root build compiled.
* c2cbd9e3e and 0badf535c (after aea484f30) added 44 root lines by hand: `PalomarBridges.X1`, 18
  `Pestov91.*`, 10 `ThompsonOre.*` and 15 `TypeA2.*`.  The wave 5 build did not compile 37 of their files;
  each is covered by an fz record: p91-palomar 0913-034120-900, p91-simple-mod-centre 0913-033826-92978,
  gq-x1-answer 0913-040618-59823, a2-palomar 0913-035442-32915, x1-palomar 0913-045040-57258.  Wave 6's
  root build compiled them.

## Wave 1 (launched 09-13 01:54, root build 0913-015433-16599, base c737ec92d): RED

108 modules, 123 newly reachable files: the initial queue, every non-LIX queue line, landed campaign
modules from `landed.log`, the census carriers, and the 01:34–01:48 green landings.  Module list:
`$NM/rw-wave1.mods`.

Result: ROOT FAILED rc=1; nothing landed.  14812 of 14816 targets built.  The only failing module is
`GGT.VanKampen.Estimating.OsinUnboundSharedEdge` (hull-unbound; landed 707c06d58, edited b52365364):
`:147:0` deterministic timeout at `whnf`; `:227:8` and `:251:10` failed to synthesize instance.

## Wave 2 (launched 09-13 02:30, root build 0913-023044-86584, base 344e3401d): GREEN, LANDED ROOT c72bdfd5d

116 modules, 135 newly reachable files: wave 1 without `OsinUnboundSharedEdge`, plus
`HullTheorem312Lemma58` (cite-hull 0913-015651), `TorsionFreeDefectNormalClosure` and `Audit.Sec5`
(audit-sec5 0913-015553), `LeavittMFQuotientBothInclusions` and `LeavittMFQuotientDiagonalSentence`
(leavitt-units 0913-014841), `SystolicProjectionClique` and `SystolicTriangleCondition` (kh-cckw
0913-015305), `SystolicDiscZip` (kh-torsion 0913-015959), `QTwoLemmaFourSixGenerators` (simple-group
0913-015349).  Module list: `$NM/rw-wave2.mods`.  Pre-flight at 6292a1395 was clean (the dupcheck `is`
hit is docstring prose).

## Wave 3 (launched 09-13 03:47, root build 0913-034741-17099, base e12190690): GREEN, LANDED ROOT ce699b9b8

17 modules, 19 newly reachable files.  Module list: `$NM/rw-wave3.mods`.  Pre-flight at cdc493958;
`nmwire.sh` built on origin e12190690, `GroupApproximation` in 253 s.  At ce699b9b8 all 17 lines are present,
before the docstring.

| module | evidence (bytes on cdc493958 = record) | owner |
|---|---|---|
| `GGT.OlshanskiiFirstVisit`, `GGT.OlshanskiiOrientedLemma25` | GREEN 0913-023524, again in 0913-025900 | hull-count94 |
| `GGT.OlshanskiiOrientedClasses` | GREEN 0913-025244, again in 0913-025900 | hull-count94 |
| `GGT.OlshanskiiOrientedBisection`, `GGT.OlshanskiiOrientedThreeClasses` | GREEN 0913-025900 | hull-count94 |
| `Kazhdan.GHWCharZeroPlaces` | GREEN 0913-033545 | ghw-charp2 |
| `Estimating.UnboundMonotoneMorseIndex`, `Estimating.UnboundOrientedWordConnectors` | GREEN 0913-034427 | sec5-sentences |
| `NonMFSentences.IntroConventionSentences`, `NonMF.Audit.Intro`, `NonMF.Audit.Sec2` | GREEN 0913-025915 | audit-intro |
| `NonMF.AffineDoublingLiteralModel`, `NonMF.Audit.Sec4` | GREEN 0913-030424 | audit-sec3 |
| `Estimating.OsinAppendixEulerMultigraph` | GREEN 0913-034435 | kh-ejz |
| `NonMF.NaiveFreeProductPropertyOfAcylindricallyHyperbolic`, `NonMFSentences.FullDefectPairLeavitt`, `Sofic.StrongConvergenceMFSubsingleton` (census carriers) | GREEN 0913-025420 | baseline-debt |

Pre-flight at cdc493958: no dangling import, no lexical sorry, no cycle.  dupcheck predicts one
collision, `GroupApproximation.Olshanskii.and`, which is docstring prose ("class and `B` is the union of
the first two") in `OlshanskiiOrientedThreeClasses.lean:193` and `OlshanskiiThreeClasses.lean:107`.
Of the 67 Lean files changed on main since 344e3401d, 21 lie in the new closure; each equals its newest
GREEN record (including `Algebra.IntegerGaussValuations`, reached through `GHWCharZeroPlaces`).

Queue entries already root-reachable, not rewired: `FinitelyPresentedInfiniteSimpleClosed`,
`SystolicDiscZip`, `SystolicDiscZipPinch`.

## Wave 4 (launched 09-13 04:22, root build 0913-042257-93245, base fa40bb30c): GREEN, LANDED ROOT f495cf119

8 modules, 10 newly reachable files.  Module list: `$NM/rw-wave4.mods`.  Pre-flight at 1a033dfb3;
`nmwire.sh` built on origin fa40bb30c: 140 GroupApproximation modules rebuilt, `GroupApproximation` in 52 s,
exit 0.  At f495cf119 all 8 lines are present (lines 4882–4889), before the docstring.

| module | evidence (bytes on 1a033dfb3 = record) | owner |
|---|---|---|
| `Estimating.OsinLemma94Pieces` | transitive: GREEN 0913-034427-9910 builds `OsinLemma94AntiparallelMetric`, which imports Pieces, and the Pieces blob at its base 5f9c16b7b equals main; also inside GREEN 0913-035614-34211 (base e1de35142) | hull-unbound |
| `Estimating.UnboundOrientedWordPolygon`, `Estimating.OsinLemma94AntiparallelMetric` | GREEN 0913-034427-9910 | sec5-sentences |
| `GGT.HullLemma35Printed` | GREEN 0913-034738-16893 | baseline-debt |
| `NonMFSentences.LeavittMFQuotientUnitsGL` (census carrier) | GREEN 0913-040613-59510 | leavitt-units |
| `OneSidedMFRadical.JacobsonComplementarySentence` (census carrier) | GREEN 0913-040230-50292 names it; the file was on its base 42d443298, blob = main | ghw-charp2, for jacobson |
| `NonMF.HullLemma510`, with `NonMF.HullFiniteRadical` | GREEN 0913-034741-17064 | cite-hull |
| `GGT.SystolicDiscMirrorFoldRestrict`, with `GGT.SystolicDiscMirrorFoldStage` | GREEN 0913-034739-16916 | fff-periodic |

Pre-flight at 1a033dfb3: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 3 build did not compile 23 files of the new closure; each has a GREEN record:

* the 10 newly reachable files above;
* 8 files changed since e12190690: `HullSCCommonQuotientCorrected`, `HullSCLemma44Canonical`,
  `HullSCLemma44JointRelabel`, `HullSCLemma49PowerDiagramFromComponents`,
  `FournierFacioParagraphFromSimpleFactor`, `HullFillTheoremCCorrected` and `TorsionFreeSectionCitations`
  from sec2-sentences 0913-025915-88905, and `Kazhdan.GHBLatticeRouteKazhdan` from kh-ejz 0913-034435-10433;
* the five files of 8e61df1ae (root lines added by other campaigns, above), from fz-integrate
  0913-034654-15072.

hull-count94's newer GREEN 0913-035614-34211 carries other `OsinLemma94AntiparallelMetric` bytes, not
landed.  That module is root-reachable since f495cf119, so landing those bytes changes the root closure.

## Wave 5 (launched 09-13 04:47, root build 0913-044703-46028, base aea484f30): GREEN, LANDED ROOT a68ab2c6c

10 modules, 11 newly reachable files.  Module list: `$NM/rw-wave5.mods`.  Pre-flight at b3a3818b5;
`nmwire.sh` built on origin aea484f30, and no root line was added between the two.  1 module rebuilt,
`GroupApproximation` in 71 s.  At e32bac3f3 all 10 lines are present.

| module | evidence (bytes on b3a3818b5 = record) | owner |
|---|---|---|
| `GGT.SystolicDiscMirrorFoldSteps`, `GGT.SystolicDiscMirrorFoldQuad`, `GGT.SystolicDiscMirrorFoldEmbed` | GREEN 0913-042826-7309 builds `Embed`, which imports `Quad`, which imports `Steps`; also GREEN 0913-040558-58001 and 0913-041349-71786 | ko-closed |
| `GGT.SystolicDiscMirrorFoldModel`, with `GGT.SystolicDiscMirrorFoldCases` | GREEN 0913-042330-95256; the `Cases` blob at its base bb5b595bb equals main.  A nonvacuity fixture: it closes no manuscript Prop | dgo-geometric |
| `NonMFSentences.IntroWitnessSignSentence` (census carrier) | GREEN 0913-041408-72676 | audit-intro |
| `VanKampen.FaceSetEarSpurCounterexample`, `VanKampen.RegionShellingSpurCounterexample` | GREEN 0913-035624-34720; the `FaceSetEar` blob at its base 4d91f2870 equals main | hull-respell, audit-sec5 |
| `NonMF.RingCompressionCellGeneral` (census carrier), `NonMF.Audit.Sec3` | GREEN 0913-040726-62527 | audit-sec3 |
| `Estimating.OsinUnboundSharedEdge` | GREEN 0913-042440-98733 (base bb5b595bb), newer than the FAILED record 0913-022343-56095 | hull-unbound |

Pre-flight at b3a3818b5: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 4 build did not compile 17 files of the new closure; each has a GREEN record:

* the 11 newly reachable files above;
* 6 files changed since fa40bb30c: `Estimating.OsinAppendixDescentInduction` and
  `Estimating.OsinAppendixSectionInduction` from hull-select 0913-042552-816;
  `TorsionFreeLeafAssembly`, `TorsionFreeLiteratureInputsLeastArea` and `TorsionFreeSaturationFromCorrected`
  from nm-endpoints 0913-030945-26927; and `Kazhdan.GHWCharZeroPlaces` from ghw-charp2 0913-044256-36897.

## Wave 6 (launched 09-13 05:02, root build 0913-050254-77102, base f2f00aada): GREEN, LANDED ROOT 1faafe122

7 modules, 14 newly reachable files.  Module list: `$NM/rw-wave6.mods`.  Pre-flight at f2f00aada, which was
also the build base.  1 module rebuilt, `GroupApproximation` in 316 s.  At e32bac3f3 all 7 lines are present.

| module | evidence (bytes on f2f00aada = record) | owner |
|---|---|---|
| `GGT.HullSCLemma51LetterPullbackCut`, with `GGT.HullSCLemma51LetterPullbackCutLift` | GREEN 0913-044157-34176; the `CutLift` blob at its base 457c543a8 equals main | debt-conditional |
| `GGT.HullSCLemma51LetterPullbackCutBlocks`, `…CutSides`, `…CutFaces`, reached through `Cut` | GREEN 0913-045018-55444 | hull-component |
| `Kazhdan.GHWTheoremFourClosed`, with `Kazhdan.GHWCharZero` and `Algebra.IntegerGridFinite`; `Kazhdan.GHWJacobsonKazhdanFinite` | GREEN 0913-045036-56628 | ghw-assembly |
| `OneSidedMFRadical.JacobsonPresented`, `OneSidedMFRadical.JacobsonPresentedSentences`, `OneSidedMFRadical.JacobsonComplementaryPresented` | GREEN 0913-045006-54503 | jacobson |
| `Estimating.OsinPocketCellArcs`, with `Estimating.OsinAppendixCutSections` | GREEN 0913-044529-42148; the `CutSections` blob at its base fbd723e92 equals main | kh-ejz |

Pre-flight at f2f00aada: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 5 build did not compile 53 files of the new closure; each has a GREEN record:

* the 14 newly reachable files above;
* 37 files rooted by hand in c2cbd9e3e and 0badf535c (root lines added by other campaigns, above);
* `GGT.SystolicDiscMirrorFoldDistinct`, made root-reachable by another landing, and
  `Kazhdan.KotowskiOllivierClosed`, changed since aea484f30: ko-closed 0913-045023-55941.

Queue entries already root-reachable, not rewired: `SystolicDiscMirrorFoldDistinct`, `KotowskiOllivierClosed`.

## Wave 7 (launched 09-13 05:43, root build 0913-054318-33163, base d18407e34): GREEN, LANDED ROOT 4a6cb4e55

9 modules, 9 newly reachable files.  Module list: `$NM/rw-wave7.mods`.  Pre-flight at e32bac3f3;
`nmwire.sh` built on origin d18407e34.  2 modules rebuilt, `GroupApproximation` in 60 s.  At 5f789a7ba all
9 lines are present.

| module | evidence (bytes on e32bac3f3 = record) | owner |
|---|---|---|
| `GGT.HullSCLemma51LetterPullbackCutOutcome`, `…CutOutcomeSides`, `…CutOutcomeRight` | GREEN 0913-050027-71372 builds them through `…Holds`; the blobs at its base 245a1c0c2 equal main.  hull-component's GREEN 0913-041859-87013, 0913-044512-41174 and 0913-045018-55444 name them | hull-component |
| `GGT.HullSCLemma51LetterPullbackHolds`, `GGT.HullSCLemma51EmbeddedBridgeHolds` | GREEN 0913-050027-71372 | hull-bridge |
| `Algebra.IntegerPlacesMinpoly` (census carrier, row b6d1590be7ab) | GREEN 0913-033545-85262 names it; also in 0913-044256-36897 | ghw-charp2 |
| `GGT.HullLemma35FreeFactors` | GREEN 0913-051219-87168 | baseline-debt |
| `GGT.SystolicDiscMirrorFoldPinchedStage` | GREEN 0913-051405-91655 names it; also in 0913-052528-4751 | fff-periodic |
| `HydeLodha.QTwoLemmaFourSixCaseTwo` | GREEN 0913-020001-45307 | kh-ejz |

Pre-flight at e32bac3f3: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 6 build did not compile 11 files of the new closure; each has a GREEN record:

* the 9 newly reachable files above;
* 2 files changed since f2f00aada: `GGT.HullLemma35Printed` from baseline-debt 0913-051219-87168 and
  `Estimating.OsinPocketCellArcs` from kh-ejz 0913-052330-1543.

`IntegerPlacesMinpoly` (queue line 414) and `QTwoLemmaFourSixCaseTwo` (queue line 377) were queued before
wave 3, and the wave 3 to 6 candidate lists missed them.  The full sweep at 00ccbca81 found no other unwired
non-LIX entry whose module is on main.

## Wave 8 (launched 09-13 06:11, root build 0913-061132-68868, base 2d25ebab5): GREEN, LANDED ROOT 830b05464

3 modules, 3 newly reachable files.  Module list: `$NM/rw-wave8.mods`.  Pre-flight at 5f789a7ba;
`nmwire.sh` built on origin 2d25ebab5.  1 module rebuilt.  At 2e11846a7, 830b05464 is an ancestor and all 3
lines are present.

| module | evidence (bytes on 5f789a7ba = record) | owner |
|---|---|---|
| `NonMF.HullCorollary73` | GREEN 0913-053322-22543, newer than the FAILED record 0913-052223-99167 | cite-hull |
| `NonMF.TheoremCAssemblyFoldLeaf` | GREEN 0913-055250-45566 (ko-closed) names it; the blob at its base 84e93eebd equals main.  theoremc-retire's GREEN 0913-034425-9721 names it too | theoremc-retire |
| `OneSidedMFRadical.JacobsonThreePlusOnePresented` | GREEN 0913-053713-26835 | jacobson |

Pre-flight at 5f789a7ba: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 7 build did not compile 5 files of the new closure; each has a GREEN record:

* the 3 newly reachable files above;
* `Kazhdan.KotowskiOllivierClosed`, changed since d18407e34 by f65f99f17 ("Close the Kotowski-Ollivier input
  from GHB(7)"), and `GGT.SystolicDiscMirrorFold`, which that version imports: ko-closed 0913-055250-45566,
  md5 = main.

Queue entries not rewired, both root-reachable: `SystolicDiscMirrorFold` (through `KotowskiOllivierClosed`)
and `KotowskiOllivierClosed`, which has its own root line.  Its bytes went through three root builds: the
wave 6 build compiled the cf1675f3b version and the wave 7 build the 4be3a3a5c version, and wave 8 compiles
f65f99f17.

## Wave 9 (launched 09-13 08:54, root build 0913-085422-44704, base 045b5f849): GREEN, LANDED ROOT 559636b4a

23 modules, 30 newly reachable files.  Module list: `$NM/rw-wave9.mods`.  Pre-flight at 2e11846a7;
`nmwire.sh` built on origin 045b5f849.  18 modules rebuilt.  At cde9049de, 559636b4a is an ancestor and all 23
lines are present.  The two Lean files changed between them,
`Estimating.OsinLemma94CaseOneWalk` and `Estimating.OsinPocketPinchedTwoGonModel`, lie outside the new
closure.  The wave checks, dupcheck and gate, rerun at 045b5f849, give the same result.

| module | evidence (bytes on 2e11846a7 = record) | owner |
|---|---|---|
| `Kazhdan.CCKWSystolicInvariantCliqueClosed` (hT6 carrier) | GREEN 0913-061054-67459, newer than the FAILED record 0913-052409 | kh-cckw |
| `GGT.HullSCGreendlingerForms`, `NonMF.TorsionFreeGreendlingerForms` | GREEN 0913-081212-8538 | hull-bridge |
| `NonMF.TorsionFreeGreendlingerSentences` | GREEN 0913-071409-41646 | hull-bridge |
| `NonMF.HullCorollary74` | GREEN 0913-081206-8349 | cite-hull |
| `NonMF.HullFreeFactorSuitable` | GREEN 0913-071556-43834 | cite-hull |
| `NonMF.TorsionFreeGreendlingerLeaf` | GREEN 0913-063820-983 | fff-periodic |
| `NonMF.TheoremCAssemblyGreendlingerLeaf` | GREEN 0913-060950-64731 | theoremc-retire |
| `Estimating.OsinLemma94PlanarPieces` | GREEN 0913-070239-32512 | hull-unbound |
| `Estimating.OsinLemma94DartMinimal` | GREEN 0913-074213-73156 (the b6bda9923 bytes; queue line 498's 88db0df7b entry was withdrawn) | sec5-sentences |
| `VanKampen.SimpleClosedWalkSides` | GREEN 0913-072751-55574, newer than the FAILED record 0913-070150 | hull-respell |
| `Estimating.OsinPocketMergeRegion` | GREEN 0913-062000-78681 | nm-endpoints |
| `Estimating.OsinPocketOuterPart`, `…Region`, `…Pieces` | GREEN 0913-034443-10848, 0913-040221-49939, 0913-073133-62116 | dgo-analytic |
| `VanKampen.SurgeryPocketGlue`, `…Count`, `…Vertices`, `…Planar` | GREEN 0913-062050-80403, 0913-070238-32448, 0913-072208-51095, 0913-074643-82657 | go-lemma42 |
| `Estimating.OsinAppendixEulerExteriorLinked` | GREEN 0913-061116-68489 | ghw-charp2 |
| `OneSidedMFRadical.JacobsonPresentedKazhdanFinite` | GREEN 0913-072919-58371, newer than the FAILED record 0913-072751 | jacobson |
| `GGT.HullLemma35Transitive`, `GGT.HullLemma35LocalFinite` | GREEN 0913-081320-10853, newer than the FAILED records 0913-075817 and 0913-080412 | baseline-debt |

Pre-flight at 2e11846a7: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 8 build did not compile 41 files of the new closure; each has a GREEN record:

* the 30 newly reachable files;
* 5 files changed since 2d25ebab5:
  * `GGT.HullSCOneStepQuasiGeodesicLeaves`: hull-respell 0913-072751-55574;
  * `Estimating.OsinAppendixAssemblyDescent`: dgo-analytic 0913-073133-62116;
  * `Kazhdan.KotowskiOllivierClosed` (queue line 512, b0ab67b4a): ko-closed 0913-065114-20727, and
    hull-bridge 0913-081212-8538, where the blob at base 296b0173f equals main;
  * `NonMF.TorsionFreeSectionAssembly`: nm-endpoints 0913-084302-12415;
  * `ThirdParty.HamSandwich.SphereOddDegree.RPnAffineCellContractible`: fz x22-palomar 0913-082342-22326;
* 6 files rooted by other campaigns since 2d25ebab5: `PalomarBridges.XXII` (fz x22-palomar
  0913-054608-34854) and `Toeplitz.{FockModule, FockSpace, GramScalars, Sections, Wick}` (fz bq-formalize
  0913-064342-9119 and 0913-074222-73251).

The template of these probes restores built modules from the Lake artifact cache, and a restored module's
empty log hides `sorry` warnings.  So the pre-flight also ran the lexical `sorry`/`admit`/`axiom` scan over
all 41 gated files, not only the newly reachable ones: 0 hits.

Not rewired: `KotowskiOllivierClosed`, which already has its own root line.

## Wave 10 (launched 09-13 10:27, root build 0913-102726-49367, base f5873fc2a): GREEN, LANDED ROOT 65d0a4497

Result: ROOT GREEN, 15048 jobs.  2 GroupApproximation modules were rebuilt and the rest restored from the
lanes' probe artifacts.  At eb314a807, 65d0a4497 is an ancestor and all 39 lines are present.

39 modules, 42 newly reachable files.  Module list: `$NM/rw-wave10.mods`.  Pre-flight at 1223d3775, with the
queue swept through line 596.  `nmwire.sh` built on origin f5873fc2a.  Five Lean files changed between the
two commits, and none of them lies in the new closure:
- `GGT.HullLemma35PieceWords`;
- `Estimating.CyclicArcSub`;
- `Estimating.OsinLemma94PendantRemoval`;
- `KirchbergPhillips.{ApproximateUnitaryEquivalence, IntertwiningLimit}`.

The wave checks, dupcheck, gate and hold scan, rerun at f5873fc2a, agree with the pre-flight.

| module | evidence (bytes on 1223d3775 = record) | owner |
|---|---|---|
| `Estimating.OsinAppendixEulerEmptyTwoGon`, `…ExteriorTwoGon`, `…SmallFaces` (Lemma 9.3 chain) | GREEN 0913-061850-77139, 0913-065054-20285, 0913-093143-91859 | hull-euler |
| `Estimating.OsinAppendixEulerCornerTwoGon`, not queued, imported by `SmallFaces` and wired ahead of it | hull-euler's GREEN 0913-093143-91859 builds it, and the blob at its base 800254639 equals main | leavitt-units |
| `Estimating.OsinAppendixEulerExteriorCellFaces`, wired ahead of `SmallFaces` | GREEN 0913-100213-68371, newer than the FAILED record 0913-095557 | hs-vanishes |
| `Estimating.OsinLemma94CaseOneWalkLists`, `…CaseOneWalkHolds` | GREEN 0913-095509-55850, which builds `Holds`, and `Holds` imports `Lists`.  It is newer than the FAILED record 0913-094857 | ko-closed |
| `Estimating.OsinLemma94ChainRespell`, `…SeparatingRemoval`, `…PolygonRealization` | GREEN 0913-090448-70090, 0913-093115-86638, 0913-095511-56070 | hull-unbound |
| `Estimating.OsinLemma94PolygonCovers`, `…PolygonCount` | GREEN 0913-093648-12289, newer than the FAILED record 0913-093132 | hull-count94 |
| `VanKampen.SurgeryInnerDiscCollapse`, `…Darts`, `…Regions`, `…Merged`; `Estimating.OsinPocketDiscMerge`, `…DiscEmptyTwoGon` | GREEN 0913-091627-32913, newer than the FAILED record 0913-090831 | fff-periodic |
| `VanKampen.SurgerySpikeDeletion`, `…Map`, `…Darts`, `…Regions`; `Estimating.OsinLemma94SpikeTransport` | GREEN 0913-093339-5579; 0913-091212-22516, newer than the FAILED record 0913-090935; 0913-093823-13569; 0913-094006-19024; 0913-095500-55040 | sec5-sentences |
| `GGT.HullLemma35Expansion`, `…Corner`, `…Sides`, `…Thin`, `…PieceGeometry` | GREEN 0913-092041-45611, newer than `Expansion`'s FAILED record 0913-091447; 0913-093041-78609; 0913-093839-14345; 0913-094811-36793 | baseline-debt |
| `Estimating.OsinPocketRegionOfSimple`, `Estimating.OsinPocketCollarOfGeodesic` | GREEN 0913-093324-3872, 0913-100702-85407 | dgo-analytic |
| `Estimating.OsinAppendixCutMerge`, `Estimating.OsinPocketTwoCollars` | GREEN 0913-090304-65564, newer than the FAILED record 0913-085704; 0913-092959-67901 | hl-lemma46 |
| `VanKampen.SimpleClosedWalkSideFaces` | GREEN 0913-090043-59913 | hull-component |
| `Estimating.OsinPocketRegionVertexSimple` | GREEN 0913-091940-39141 | hull-bridge |
| `Estimating.OsinLemma94RegionSideCount` | GREEN 0913-091959-40244 | audit-intro |
| `Estimating.OsinLemma94InsertionTransport` | GREEN 0913-094211-23583, newer than the FAILED record 0913-093536 | sec2-sentences |
| `Estimating.OsinCConditionLineModel` | GREEN 0913-093823-13550 | audit-sec3 |
| `VanKampen.SurgeryPocketGlueFaces` | GREEN 0913-094529-34532, newer than the FAILED record 0913-093031 | go-lemma42 |
| `Estimating.OsinPocketZeroCellMergeFalse` | GREEN 0913-094902-38721 | hull-select |

Pre-flight at 1223d3775: no dangling import, no lexical sorry, no cycle; dupcheck predicts no collision.
The wave 9 build did not compile 58 files of the new closure (59 at the pre-flight, counting
`OEquivalentCellFaces`):

* the 42 newly reachable files;
* 11 files rooted by other campaigns since 045b5f849:
  * `CStarLimits.TowerLift`: fz ko-limits 0913-092350-50956;
  * `CuTensor.{CuZModel, CuZModelCompact, ObstructionGrothendieck, RankTwoObstruction, WayBelow}`: fz
    x95-obstruction 0913-091125-21023;
  * `KTheory.{K1Functorial, K1Scalar}`: fz ko-k1 0913-095850-65227 and 0913-094358-29653;
  * `KTheory.Suspension`: fz ko-bott 0913-092439-53870;
  * `KirchbergAlgebra.{Basic, CuntzCriterion}`: fz l-kirchberg 0913-094230-24665;
* 5 files changed since 045b5f849:
  * `Estimating.OsinLemma94PlanarPieces`: hull-unbound 0913-090448-70090;
  * `Estimating.OsinPocketPieces`: dgo-analytic 0913-093324-3872;
  * `NonMF.HullCorollary73`: cite-hull 0913-084125-2235;
  * `Pestov91.Assembly` and `Pestov91.RingSimple`, below.

`Pestov91.Assembly` and `Pestov91.RingSimple` are root-reachable, and the Pestov 9.1 commits 33c61859c and
95632338d changed them.  The gate finds no record for their bytes in `$NM/lanes` or `fz/lanes`:
- `Assembly`'s bytes are covered by the pc campaign's GREEN record ex-palomar-hygiene 0913-091934-38820
  (md5 = main).
- No record carries `RingSimple`'s current bytes, but the change is prose inside comments.  With comments
  stripped (nesting-aware), its code is identical to 045b5f849's, and the comment delimiters balance.

The wave 10 root build compiles both files.

The lexical `sorry`/`admit`/`axiom` scan over all 58 gated files finds nothing.

Queue entries not rewired, all already root-reachable:
- `OsinPocketPieces` (lines 534 and 555); its bytes are gated;
- `OsinAppendixEulerCount`, `…Exterior`, `…ExteriorCount` and `CombMapRestrictionFaceClasses` (lines 573–575
  and 578).

Queued after the wave 10 sweep and wired in wave 11:
- `Estimating.OsinLemma94PendantRemoval` (jacobson);
- `Estimating.CyclicArcSub` (sec2-sentences);
- `GGT.HullLemma35PieceWords` (baseline-debt).

## Wave 11 (launched 09-13 11:20, root build 0913-112021-31550, base 23348780a): GREEN, LANDED ROOT 9eba4d854

Result: ROOT GREEN, 15063 jobs.  1 GroupApproximation module was rebuilt and the rest restored from the
lanes' probe artifacts.  At 520f03021, 9eba4d854 is an ancestor and all 5 lines are present.

Recheck at the build base 23348780a, where 11 Lean files had landed after eb314a807:
- the wave checks, dupcheck (closure 6403 → 6408) and hold scan agree with the pre-flight;
- the gate needs evidence for 6 more files that other campaigns had rooted since f5873fc2a, each covered by
  an fz record:
  - `CuTensor.{CuntzSubequiv, ObstructionCuntzProjection, ObstructionFinite}`: fz x95-obstruction
    0913-095415-50899;
  - `KTheory.K1Lift`: fz ko-k1 0913-095850-65227;
  - `KirchbergPhillips.{ApproximateUnitaryEquivalence, IntertwiningLimit}`: fz l-kp 0913-100215-68480;
- the lexical scan over all 15 gated files finds nothing.

5 modules and 5 newly reachable files, from queue lines 599, 601, 602, 604 and 605.  Module list:
`$NM/rw-wave11.mods`.  Pre-flight at eb314a807, with the queue swept through line 605.  `nmwire.sh` built on
origin 23348780a.

| module | evidence (record md5 = bytes on eb314a807) | owner |
|---|---|---|
| `Estimating.CyclicArcSub` | GREEN 0913-102559-44269, newer than the FAILED record 0913-101514 | sec2-sentences |
| `Estimating.OsinLemma94PendantRemoval` | GREEN 0913-102123-19053 | jacobson |
| `GGT.HullLemma35PieceWords` | GREEN 0913-101453-98311 | baseline-debt |
| `Estimating.OsinPocketGlueDiagram` | GREEN 0913-102750-50297, newer than the FAILED record 0913-101623 | go-lemma42 |
| `Estimating.OsinPocketMultipleEdgeTransport` | GREEN 0913-104724-79095 | hl-lemma46 |

Pre-flight at eb314a807:
- no dangling import, no lexical sorry and no cycle;
- no candidate imports another;
- dupcheck predicts no collision (closure 6397 → 6402).

The wave 10 build did not compile 9 files of the new closure:
- the 5 new files;
- 4 files rooted by other campaigns since f5873fc2a:
  - `KTheory.{K0Basic, K0Rect}`: fz ko-k0 0913-095450-54053;
  - `KTheory.{TensorKronecker, TensorProduct}`: fz ko-tensor 0913-095402-49657.

No file in the closure changed since f5873fc2a.  The lexical `sorry`/`admit`/`axiom` scan over the 9 gated
files finds nothing.

## Wave 12 (launched 09-13 12:07, root build 0913-120704-62031, base c57399ded): GREEN, LANDED ROOT 141bea9e6

Result: ROOT GREEN, 15069 jobs.  1 GroupApproximation module was rebuilt and the rest restored from the
lanes' probe artifacts.  At ea02cc1c6, 141bea9e6 is an ancestor and all 5 lines are present.

5 modules and 6 newly reachable files, from queue lines 606–609 and 611.  Module list: `$NM/rw-wave12.mods`.
Pre-flight at 8f13c3af4, with the queue swept through line 611.  `nmwire.sh` built on origin c57399ded.

| module | evidence (record md5 = bytes on 8f13c3af4) | owner |
|---|---|---|
| `VanKampen.SurgeryCornerJoinMap`, `…CornerJoinDiagram` (`Diagram` imports `Map`) | GREEN 0913-111152-20791 builds both.  `Map` also has GREEN 0913-105542-93925, newer than its FAILED record 0913-103751 | hull-bridge |
| `GGT.HullLemma35PieceSides` | GREEN 0913-104731-79425 | baseline-debt |
| `Estimating.OsinPocketMultipleEdgeAssembly`, and `Estimating.OsinPocketRegionSide`, which it imports | GREEN 0913-111924-29328.  `RegionSide`'s blob at the record's base 661fd5216 equals main | hull-select |
| `VanKampen.SurgeryMonogonDoubling` | GREEN 0913-111910-27612, newer than the FAILED record 0913-105724 | fff-quotient |

Pre-flight at 8f13c3af4:
- no dangling import, no lexical sorry and no cycle;
- dupcheck predicts no collision (closure 6408 → 6414);
- the gate needs evidence only for the 6 newly reachable files.  No root line was added by others and no
  closure file changed since 23348780a;
- the lexical scan over the 6 gated files finds nothing.

Recheck at the build base c57399ded agrees with the pre-flight: wave checks, dupcheck, gate, holds and lexical
scan.  5 Lean files landed after 8f13c3af4, none in the new closure:
- `GGT.HullLemma35Letter`;
- `Estimating.OsinLemma94{PolygonLists, SeparatedInsertion}`;
- `RotationAlgebra.{DirectSummand, TorusRetraction}`.

## Wave 13 (launched 09-13 13:36, root build 0913-133632-59092, base 03f8f2c88): GREEN, LANDED ROOT e0dcf8b99

Result: ROOT GREEN at 13:51, 15120 jobs.  6 GroupApproximation modules were rebuilt and the rest restored from the
lanes' probe artifacts.  At 8bbf0a9c8, e0dcf8b99 is an ancestor and all 30 lines are present (root 5049
import lines).

30 modules and 32 newly reachable files.  The wave takes every queue line not in root 141bea9e6
(lines 613–649), plus 8 modules that no queue line starts with.  Each of those 8 goes in just ahead of the
modules that import it.  Module list: `$NM/rw-wave13.mods`.  Pre-flight at 1b6c528fa, with the queue swept
through line 649.  `nmwire.sh` built on origin 03f8f2c88.

Root lines added for modules that no queue line starts with.  Each is on main and has a GREEN record that
covers its bytes.

| module | why | record | owner |
|---|---|---|---|
| `Estimating.OsinLemma94{PolygonLists, PolygonKinds, PolygonSides, PolygonMaximal, PolygonPartition}` | The lead named the closed partition chain (746028b24).  Line 649 `SectionResiduals` imports `PolygonPartition` | GREEN 0913-111016-12907, 0913-120932-63752, 0913-125822-38552, 0913-131655-32736, 0913-132334-2532.  The last three are newer than the FAILED records 0913-125058, 0913-130838 and 0913-132143 | ghw-assembly |
| `VanKampen.SurgeryGeodesicCollarAssembly` | Order hold of line 644.  `MonogonDoublingStrip` and `CollarJoin` both import it | GREEN 0913-115929-47047 | kh-torsion |
| `Estimating.OsinPocketSectionFaceSet` | Order hold of line 640, before `OsinPocketCellWalk`.  It brings in `OsinPocketGapArcs` and `NoncrossingClosedWalkSides` (jacobson 0913-130857-87977) | GREEN 0913-130217-56077, newer than the FAILED record 0913-093343 | kh-ejz |
| `Estimating.OsinUnboundCaseOneFace` | Line 642 lists it as a prerequisite of `CaseTwo` | GREEN 0913-133025-35313 | hull-unbound record |

Queued modules.  The record is the newest GREEN covering the bytes on 1b6c528fa, and each is newer than
every FAILED record for the module:

| module | line | record | owner |
|---|---|---|---|
| `GGT.HullLemma35Letter`, `GGT.HullLemma35Closed` (`Closed` imports `Letter`) | 613, 625 | 0913-114118-23523, 0913-123731-5219 | baseline-debt |
| `Estimating.OsinLemma94SeparatedInsertion` | 615 | 0913-113234-56193 | sec5-sentences |
| `Estimating.OsinLemma94CellArcs` | 617 | 0913-104724-79090 | ko-closed |
| `Estimating.OsinLemma94CuttingChains`, `…QuasiGeodesicRespell` | 620, 621 | 0913-111910-27621, 0913-120651-61632 | hull-unbound |
| `Estimating.OsinLemma94BoundaryArcs` | 622 | 0913-111012-12718 | cite-hull |
| `Estimating.OsinLemma94CornerInsertion` | 623 | 0913-123745-5546 | simple-group |
| `Estimating.OsinLemma94WordRespelling` | 624 | 0913-101505-99170 | hull-component |
| `Estimating.OsinAppendixEulerSection` | 627 | 0913-125857-40608 | hull-euler |
| `Estimating.OsinAppendixEulerTwoGonLabels` | 629 | 0913-125826-38654 | debt-conditional |
| `VanKampen.OEquivalentCellFaces` (released, see Held) | 631 | 0913-113305-58468 | sec2-sentences |
| `Estimating.OsinLemma94SeparatedInsertionProof` | 635 | 0913-131141-4967 | sec2-sentences |
| `Estimating.OsinPocketGlueEquivalence` (imports `OEquivalentCellFaces`) | 637 | 0913-125816-38320 | go-lemma42 |
| `Estimating.OsinAppendixEulerCornerTwoGonCount`, `…CornerTwoGonSection` (`Section` imports `Count` and `OsinAppendixEulerSection`) | 638, 639 | 0913-130413-64412, 0913-130704-80770 | leavitt-units |
| `Estimating.OsinPocketCellWalk` | 641 | 0913-130857-87977 | jacobson |
| `Estimating.OsinLemma94CaseTwo` | 643 | 0913-131149-5355 | sec5-sentences |
| `VanKampen.SurgeryMonogonDoublingStrip` | 645 | 0913-131547-23242 | fff-quotient |
| `GGT.DGOProposition435PrintedCounterexample` | 646 | 0913-132138-96143 | baseline-debt |
| `VanKampen.SurgeryGeodesicCollarJoin` | 647 | 0913-132438-5905 | hull-bridge |
| `Estimating.OsinLemma94SectionResiduals` (line 649's 4002b9371 bytes supersede line 633) | 633, 649 | 0913-133025-35313 | hull-unbound |

Order holds, checked from the import closure at 1b6c528fa.  Every in-wave import of a module comes before it:
- `MonogonDoublingStrip` comes after `SurgeryMonogonDoubling` (a root line since wave 12) and after
  `SurgeryGeodesicCollarAssembly`;
- `OsinPocketCellWalk` comes after `OsinPocketSectionFaceSet`;
- `CaseTwo` comes after `SeparatedInsertion`, `SeparatedInsertionProof`, `CuttingChains` and
  `OsinUnboundCaseOneFace`.  Its other listed prerequisites are already root lines: `SeparatingRemoval`,
  `PendantRemoval`, `CaseOneWalkHolds`, `UnboundNonemptyConnectors` and `DGOPolygonGeodesicChain`;
- `SectionResiduals` is last.  It comes after `CaseTwo`, the partition chain, `CornerInsertion`, `BoundaryArcs`,
  `CuttingChains`, `QuasiGeodesicRespell` and `CellArcs`.

Pre-flight at 1b6c528fa:
- no dangling import, no lexical sorry and no cycle;
- dupcheck predicts no collision (closure 6433 → 6465);
- the gate needs evidence for 57 files.  51 were not compiled by build c57399ded: the 32 newly reachable files
  and 19 root lines other campaigns added.  6 have changed since then: `HullLemma35Printed`,
  `OsinLemma94{AntiparallelMetric, Pieces, PlanarPieces, PolygonCount}` and `OsinPocketPieces`.  A GREEN
  record covers every one;
- 0 held;
- the lexical scan over the 57 gated files finds nothing.

The first pass at ea02cc1c6 took only the 22 queued modules, and it also passed.  Then line 649 changed
`SectionResiduals` so that it imports `CaseTwo` and `PolygonPartition`, and the pre-flight was run again.

Recheck at the build base 03f8f2c88 agrees with the pre-flight.  1b6c528fa is an ancestor, and no
GroupApproximation file or root line changed in between.  The wave checks and dupcheck match (closure
6433 → 6465, no collision).  The gate's evidence lines are identical, with nothing held, and the lexical scan
over the 57 gated files finds nothing.

## Wave 14 (launched 09-13 14:17, root build 0913-141703-40545, base 80df00345): GREEN, LANDED ROOT 80007c036

Result: ROOT GREEN at 14:28, 15133 jobs.  15 GroupApproximation modules were rebuilt and the rest restored from the
lanes' probe artifacts.  At 991380d00, 80007c036 is an ancestor and all 12 lines are present (root 5061
import lines).

12 modules and 13 newly reachable files.  The wave takes every queue line not in root e0dcf8b99 (lines
652–669).  `FaceSetCircuitNoncrossing` brings in `OsinPocketRegionUnpinched`, which is not a root line
(dgo-geometric, GREEN 0913-140543-86239 at base 037386a74).  Module list: `$NM/rw-wave14.mods`.  Pre-flight at
e48f35d1e, with the queue swept through line 669.  `nmwire.sh` built on origin 80df00345.

Modules in wire order.  The record is the newest GREEN covering the bytes on e48f35d1e.  Records for modules
marked released are older than ghw-charp2's FAILED co-probe (see Held); every other record is newer than
every FAILED record for its module.

| module | line | record | owner |
|---|---|---|---|
| `Estimating.OsinAppendixEulerTwoGonFaceClass` (released) | 652 | 0913-134440-98829 | debt-conditional |
| `Estimating.OsinPocketGlueOuterArc`, `…GlueOuterTransport` (`Transport` imports `Arc`; both released) | 654, 655 | 0913-134953-22063 | hull-select |
| `Estimating.QuasiGeodesicValueOneGap` | 656 | 0913-134955-22334 | hull-component |
| `Estimating.OsinLemma94ShortSides` (released) | 658 | 0913-135154-29800 | sec5-sentences |
| `VanKampen.FaceSetCircuitNoncrossing` | 659 | 0913-135519-45680 | cite-hull |
| `Estimating.OsinPocketKeptCell` | 661 | 0913-140023-67387 | sec2-sentences |
| `Estimating.OsinLemma94OneCellValue` | 663 | 0913-135819-58619 | ko-closed |
| `Estimating.OsinPocketLoopCut` | 665 | 0913-135346-38278 | jacobson |
| `Estimating.OsinPocketRegionNoncrossingWalk` | 666 | 0913-140151-74557 | dgo-analytic |
| `VanKampen.SurgeryOuterSpurThickening` | 668 | 0913-140848-97054 | hs-vanishes |
| `Estimating.OsinLemma94BudgetFilter` | 669 | 0913-134955-22334 | hull-component |

The 14:00 rulings say `BudgetFilter` lands only if hull-count94 consumes it.  It was on main at e48f35d1e and
queued, so it is in the wave.

Order holds, checked from the import closure at e48f35d1e.  Every in-wave import of a module comes before it,
so `GlueOuterTransport` comes after `GlueOuterArc`.  At 80df00345, every module named in a wire-after comment
is already a root line, and the candidate imports it directly:
- `ShortSides`: `OsinLemma94PlanarPieces`, `OsinLemma94RegionSideCount`;
- `OneCellValue`: `GGT.OsinPenetration`, `VanKampen.FaceShellingValue`, `OsinPocketCellArcs`,
  `OsinPocketMergeRegion`;
- `LoopCut`: `OsinPocketMultipleEdgeAssembly`.

Pre-flight at e48f35d1e:
- no dangling import, no lexical sorry and no cycle;
- dupcheck predicts no collision (closure 6465 → 6478);
- the gate needs evidence for 16 files: the 13 newly reachable files, and 3 files changed since build
  03f8f2c88 (`NonMF.TorsionFree{LeafAssembly, SectionAssemblyClosedGO, SectionSentences}`, nm-endpoints
  0913-133143-40961).  A GREEN record covers every one;
- 5 held, all released by closure identity (see Held);
- the lexical scan over the 16 gated files finds nothing.

Earlier passes at 8bbf0a9c8 and 854abfaa8 took the 10 lines through 666 and gave the same 5 holds.  Lines 668
and 669 arrived at e48f35d1e.

Recheck at the build base 80df00345 agrees with the pre-flight.  e48f35d1e is an ancestor.  The only
GroupApproximation change in between adds `OsinPocketPinchedTwoGonNoncrossingRegion`, outside the new closure.
The wave checks and dupcheck match (closure 6465 → 6478, no collision), and the 5 holds are identical.  The
gate's evidence lines match except for two newer covers: `OsinPocketRegionNoncrossingWalk` and
`OsinPocketRegionUnpinched` are now covered by dgo-geometric's GREEN 0913-141525-34391 at base 80df00345.  Each released module's closure is still byte-identical to its GREEN record's inputs,
and the lexical scan over the 16 gated files finds nothing.

## Wave 15 (launched 09-13 14:54, root build 0913-145410-71222, base ed724988b): GREEN, LANDED ROOT 074e7a200

Result: ROOT GREEN at 15:03, 15143 jobs.  One GroupApproximation module was rebuilt and the rest restored from the
lanes' probe artifacts.  The 10 import lines went in after root line 5122.  At a29b02280, 074e7a200 is an ancestor
and all 10 lines are present at lines 5123–5132 (root 5071 import lines).

10 modules and 10 newly reachable files, from queue lines 670–688 and 692.  Launched after ghw-charp2's (A)
landing f04929ebb.  The record is the newest GREEN covering the landed bytes at the build base, and each record's
`# PROBE` line reads GREEN.

| module | line | record at ed724988b | owner |
|---|---|---|---|
| `Estimating.OsinPocketGlueCarriers`, `…GlueCellTransport` | 673, 674 | 0913-144505-9146 (ghw-charp2 (A)) | go-lemma42 |
| `Estimating.OsinPocketPinchUnpinched`, `…PinchSplit` | 676, 677 | 0913-144505-9146 (ghw-charp2 (A)) | kh-cckw |
| `Estimating.OsinPocketCutResiduals` (line 682's 5ef75ffa7 supersedes line 670) | 670, 682 | 0913-144505-9146 (ghw-charp2 (A)) | dgo-analytic |
| `Estimating.OsinLemma94OneCellMorse` | 684 | 0913-145215-56485 (ko-closed) | ko-closed |
| `Estimating.OsinDescentResiduals` | 685 | 0913-145357-69970 (ghw-assembly) | dgo-analytic |
| `Estimating.OsinLemma94PolygonClasses` | 686 | 0913-144505-9146 (ghw-charp2 (A)) | hull-count94 |
| `Estimating.OsinGreendlingerOpenResiduals` | 688 | 0913-144505-9146 (ghw-charp2 (A)) | ghw-assembly |
| `SurgeryNoncrossingCollarWalk` | 692 | 0913-144452-8341 (fff-quotient) | fff-quotient |

Skipped: lines 678, 680 and 689, fff-periodic's `OsinUnboundSameCellPocket`, `OsinUnboundSameCell` and
`OsinUnboundSameCellBridge`.  None of them is probed yet.

Two covers need a word:
- ghw-assembly's newer GREEN 0913-145357-69970 probed different bytes of `OsinGreendlingerOpenResiduals`.  The wave
  wires the landed 8a07ad7d0 bytes, and the older ghw-charp2 record covers those.
- fff-quotient's GREEN is newer than its FAILED probe 0913-144235 of `SurgeryNoncrossingCollarWalk`, so the module is
  not held.

Order holds, from the import closure at bec8c0538 and again at ed724988b.  Every in-wave import of a module comes
before it:
- `GlueCellTransport` comes after `GlueCarriers`, and `PinchSplit` after `PinchUnpinched`;
- `CutResiduals`, `DescentResiduals` and `GreendlingerOpenResiduals` come in that order, after the glue pair;
- `OneCellMorse` comes after `OneCellValue`, a root line since wave 14;
- `SurgeryNoncrossingCollarWalk` imports no wave module.

Pre-flight at bec8c0538, after (A), and recheck at the build base ed724988b:
- (A) is on main: all 31 overlay files of ghw-charp2's GREEN co-probe 0913-143304-32295 match;
- no dangling import, no lexical sorry and no cycle;
- dupcheck predicts no collision (closure 6478 → 6488);
- the gate needs evidence for 34 files, and a GREEN record covers every one:
  - the 10 newly reachable files;
  - 24 rooted files changed since wave 14's build base 80df00345, which are the 24 of (A)'s 27 files inside the
    closure;
  - at bec8c0538, ghw-charp2 0913-144505-9146 (base 514b76e75, 183 modules) covers all 34;
  - at ed724988b, ghw-assembly 0913-145357-69970 (base 6622fce2b) is the newer cover of 8 files (7 (A) files and
    `OsinDescentResiduals`), and ko-closed 0913-145215-56485 is the newer cover of `OneCellMorse`;
- 0 held;
- the lexical scan over the 34 gated files finds nothing.

The earlier pre-flight at 991380d00, before (A), had 9 modules and 9 gated files, with the same result.  Queue line
692 came in after (A) and joined on its own clean pre-flight at bec8c0538.

## Wave 16 (launched 09-13 16:13, root build 0913-161309-41278, base ddde33648): building

31 modules and 41 newly reachable files, from queue lines 694–757.  Pre-flight at db9a29cbf, after wave 15's
landing 074e7a200.  The record is the newest GREEN covering the landed bytes at the build base, and each record's
`# PROBE` line reads GREEN.

| module | line | record at ddde33648 | owner |
|---|---|---|---|
| `Estimating.OsinLemma94OneCellFace` | 694 | 0913-145215-56485 (ko-closed) | ko-closed |
| `SurgeryNoncrossingCollarWalkSides` | 699 | 0913-153039-58042 (fff-quotient) | fff-quotient |
| `Estimating.OsinLemma94ClassRuns` | 701 | 0913-145849-94334 (audit-intro) | audit-intro |
| `Estimating.OsinPocketKeptCellUnpinched` | 703 | 0913-150326-35154 (baseline-debt) | baseline-debt |
| `NoncrossingClosedWalkEuler` | 706 | 0913-155924-73125 (sec2-sentences) | hull-euler |
| `Estimating.OsinPocketPinchSplitWalk` | 709 | 0913-153737-1399 (go-lemma42) | kh-cckw |
| `SurgeryGeodesicCollarDouble` | 711 | 0913-155533-35125 (simple-group) | kh-torsion |
| `Estimating.OsinLemma94OneCellWindow` | 713 | 0913-150725-78874 (ko-closed) | ko-closed |
| `SurgeryGeodesicCollarInsert` | 714 | 0913-155611-43423 (hull-bridge) | hull-bridge |
| `SurgeryNoncrossingCollarStrip`, `…CollarStripModels` | 717, 718 | 0913-153039-58042 (fff-quotient) | fff-quotient |
| `Estimating.OsinPocketKeptCellAbsorbed` | 720 | 0913-155924-73125 (sec2-sentences) | sec2-sentences |
| `Estimating.OsinLemma94GapFreeWords` | 723 | 0913-150235-20084 (hull-unbound) | hull-unbound |
| `Dynamics.ClopenCrossedProduct`, `…ClopenDefectPair` | 726, 727 | 0913-154019-19595 (chain-core) | chain-core |
| `Estimating.OsinPocketMultipleEdgeLakeModel` | 729 | 0913-154539-52051 (dgo-analytic) | dgo-analytic |
| `Estimating.OsinUnboundSameCell`, `…SameCellSegments` | 680, 730, 732 | 0913-155114-84940 (fff-periodic) | fff-periodic |
| `Algebra.DirectlyFiniteCorner` | 735 | 0913-160055-80827 (chain-reflection) | chain-reflection |
| `Estimating.OsinPocketCopyWalk` | 737 | 0913-153809-4154 (leavitt-units) | leavitt-units |
| `Dynamics.SubshiftLanguageStabilization` | 738 | 0913-155918-72707 (chain-subshift) | chain-subshift |
| `Estimating.OsinPocketLakeLabelledModel` | 740 | 0913-155026-81505 (audit-sec3) | audit-sec3 |
| `Algebra.LEFRingDirectedUnion` | 742 | 0913-160055-80827 (chain-reflection) | chain-itinerary |
| `Dynamics.SubshiftWordGraph` | 745 | 0913-155918-72707 (chain-subshift) | chain-words |
| `Estimating.OsinPocketKeptCellNoncrossing` | 747 | 0913-155924-73125 (sec2-sentences) | sec2-sentences |
| `SurgeryGeodesicCollarReduction` | 748 | 0913-155611-43423 (hull-bridge) | hull-bridge |
| `Algebra.SkewMonoidAlgebraCoefficientMap` | 749 | 0913-155549-37754 (chain-itinerary) | chain-itinerary |
| `Estimating.OsinLemma94PinchedQuadrilateral` | 751 | 0913-160048-79943 (hull-unbound) | hull-unbound |
| `Algebra.DirectlyFiniteReflection` | 753 | 0913-160055-80827 (chain-reflection) | chain-reflection |
| `Dynamics.ChainRecurrence` | 755 | 0913-160538-94022 (hull-euler) | hull-euler |
| `Estimating.OsinPocketOuterSpur` | 757 | 0913-160514-92421 (kh-cckw) | kh-cckw |

Skipped:
- line 707, hull-component's `OsinLemma94ClassCovers` (13cf15e1a), held on main's 15:50 order.  It is red against
  hull-count94's `PolygonClasses` respell a25fe2383, where `ClassCovers` takes `M L`, and it waits for a GREEN
  record of the fixed bytes.  At ddde33648 no module imports it, and it is the only importer of `PolygonClasses`;
- lines 678 and 689, fff-periodic's `OsinUnboundSameCellPocket` and `OsinUnboundSameCellBridge`, which have no
  GREEN probe yet;
- lines 758–765 (chain-subshift's `RetainedSubshift`, `NoncyclicEdgeDefect` and `CoreSubshift`, sec5-sentences'
  `OsinLemma94ClassTransitions`, fff-periodic's `OsinUnboundSameCellSides`), which arrived after the pre-flight.

Three covers need a word:
- `OsinUnboundSameCell` and `…Segments`: queue lines 731 and 733 still say "probe pending".  fff-periodic's GREEN
  0913-155114-84940 covers the main bytes and is newer than its FAILED probes 0913-150904-97612 and
  0913-152931-54308.
- The gate's newest cover for `OsinGreendlingerOpenResiduals` and `OsinUnboundCaseOneRun` is theoremc-retire's S5
  co-probe 0913-153647-93989.  That record is GREEN, but queue line 724 withdraws its bytes.  Older GREEN records
  cover the same bytes by md5.  ghw-assembly 0913-145357-69970 covers the waist 5f031e3a6.  theoremc-retire's
  T-window probe 0913-145812-91168 covers `CaseOneRun`, and also `CaseOneFace`, `Pieces` and `PlanarPieces`.
- `OsinLemma94PolygonClasses` (a25fe2383): hull-count94's GREEN 0913-152533-28063 matches the main bytes.  The
  gate's newest cover is hull-unbound 0913-160048-79943.

Order holds, from the import closure at db9a29cbf and again at ddde33648.  Every in-wave import of a module comes
before it:
- `SurgeryNoncrossingCollarStrip` comes after `CollarWalkSides` and `GeodesicCollarDouble`, and `CollarStripModels`
  after `CollarWalkSides`;
- `ClopenDefectPair` comes after `ClopenCrossedProduct`, and `SameCellSegments` after `SameCell`;
- `KeptCellNoncrossing` comes after `NoncrossingClosedWalkEuler` and `KeptCellAbsorbed`, and
  `GeodesicCollarReduction` after `GeodesicCollarInsert`;
- `DirectlyFiniteReflection` comes after `DirectlyFiniteCorner` and `LEFRingDirectedUnion`.

Pre-flight at db9a29cbf, and recheck at the build base ddde33648:
- no dangling import, no lexical sorry and no cycle;
- dupcheck predicts no collision (closure 6489 → 6530);
- the gate needs evidence for 52 files, and a GREEN record covers every one:
  - the 41 newly reachable files: the 31 modules and 10 files they bring in (`OsinPocketEdgeDoubling`,
    `…LakeAbsorption`, `…LakeModel`, `…PinchStep`, five `OsinPocketPinchedTwoGon*` files and
    `SurgeryGeodesicCollarWalk`);
  - `OsinUnboundCaseOneRun`, which is root-reachable at the build base but was not compiled by wave 15's build;
  - 10 rooted files changed since wave 15's build base ed724988b: five `OsinAppendix*` files,
    `OsinGreendlingerOpenResiduals`, `OsinLemma94{Pieces, PlanarPieces, PolygonClasses}` and
    `OsinUnboundCaseOneFace`;
- 0 held;
- the lexical scan over the 52 gated files finds nothing.

Recheck at the build base ddde33648 agrees with the pre-flight.  db9a29cbf is an ancestor.  The only
GroupApproximation changes in between add `Dynamics.{RetainedSubshift, NoncyclicEdgeDefect, CoreSubshift}` and
`OsinUnboundSameCellSides`, all outside the new closure.  The wave checks and dupcheck match.  The gate's evidence
lines match except for two newer covers: chain-subshift 0913-155918-72707 now covers `SubshiftLanguageStabilization`
and `SubshiftWordGraph`, and fff-periodic 0913-161159-35900 covers `OsinAppendixSections`.

The earlier pass at 6b494013f took the 20 lines through 737 and gave the same result (closure 6489 → 6517, 39 gated
files, 0 held).

### Held

| module | reason | owner |
|---|---|---|
| `CharClass.*`, `Analysis.LIX*`, `ProblemLIXStrongAssemblyHalves` | LIX campaign files, in flight in the shared tree | LIX lanes |
| `Estimating.OsinLemma94ClassCovers` | red against `PolygonClasses` a25fe2383 (`ClassCovers` takes `M L`); main's 15:50 hold until the fixed bytes have a GREEN record | hull-component |

Released in wave 14 by closure identity: `Estimating.OsinAppendixEulerTwoGonFaceClass`,
`…OsinPocketGlueOuterArc`, `…OsinPocketGlueOuterTransport`, `…OsinLemma94ShortSides`, and the root line
`Manuscript.NonMF.TorsionFreeSectionAssemblyClosedGO`.
- ghw-charp2's LoopCut (A) co-probe 0913-135734-55169 (164 modules, base 67ec49f02) named all five and FAILED
  rc=1, so the hold rule flagged them.
- Its log shows errors only in `OsinLemma94OneCellValue`, `OsinAppendixEulerTwoGonLabels`, `OsinPocketPinchSplit`
  and `OsinPocketKeptCell`.
- At 80df00345, each released module's full import closure (1163 to 1919 files) is byte-identical to the inputs
  of a GREEN record: 0913-134440-98829, 0913-134953-22063 (both glue modules), 0913-135154-29800 and
  0913-133143-40961.  `lean-toolchain` and `lake-manifest.json` equal those at the records' bases.
- The red probe's inputs differ from main in 1 to 5 overlay files of each closure, `OsinAppendixSections` in every
  case.

Released in wave 13: `VanKampen.OEquivalentCellFaces`, held in waves 10–12.  Its only probe record had been
FAILED 0913-101514-99667.  The newer GREEN record 0913-113305-58468 (queue line 630) covers the main bytes.
That run replayed this module's olean from 0913-101514-99667, where this file built with no error.

Released from the wave 4 holds, all in wave 5: `NonMF.Audit.Sec3` (audit-sec3's green bytes landed at
80abe6604), `Estimating.OsinUnboundSharedEdge` (new green probe), `GGT.SystolicDiscMirrorFoldSteps`.

## Stale notes superseded

* wire-queue line 318 "GHBHyperbolicDiscCounts waits on red Filling/Counts": Counts and Filling are
  green at 4c12845a1 (systolic-counts report).
* `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`: renamed in
  6a5f25704; both are in wave 1.
* Wave 4 of 09-12 (40 modules) never landed; its modules are in wave 1.
* root-wire's 01:58 message to main said `SystolicProjectionClique` was held on red bytes on main;
  kh-cckw's green bytes landed minutes later, and the module landed in wave 2.
* The 03:13 audit-sec3 queue line for `Audit.Sec3` cites probe 0913-025304-66495 as GREEN; that record
  says FAILED rc=1.
* Eight queue lines give old module paths.  Lines 53–55
  `Manuscript.NonMF.TorsionComplementaryIdempotents{Sentences, Jacobson, Ideal}` are now under
  `Manuscript.OneSidedMFRadical`; line 98 `GGT.GerasimovaOsinLemma43` is `Manuscript.NonMF.GerasimovaOsinLemma43`;
  lines 104–107 `Algebra.{FoxComplexZ, FoxComplexLowExact, FreeGroupFoxHomotopy, FoxFreeCalculus}` are
  under `Kazhdan`.  At e32bac3f3 all eight modules are root-reachable under the current paths.
* root-wire's 05:06 queue note said 38 of the 53 wave 6 files were rooted by hand in c2cbd9e3e and
  0badf535c; 37 were, and the 38th file rooted by others was `SystolicDiscMirrorFoldDistinct`.
