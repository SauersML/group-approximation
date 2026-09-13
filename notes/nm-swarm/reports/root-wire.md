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
* `rw/rwtool.py <sha> census`: census tokens resolved to declaring files; carriers whose files are not
  root-reachable.

## 09-13 root state (origin/main 1a033dfb3, 04:20)

* Root at ce699b9b8 (wave 3): 4816 GroupApproximation import lines, all before the module docstring (OK);
  no missing module, no duplicate line; closure 6214 modules; 0 dangling imports inside it.  352 modules on
  main are not reachable from the root (356 at cdc493958, 449 at 6292a1395).
* 8e61df1ae (another campaign, 04:03, "root the GKP 4.2 endpoint") added four root lines by hand,
  `CommutingSoficActions.{DiagonalRestriction, Endpoint, FreeActionSofic, KunThomCosetAction}`, and changed
  the docstring of `Algebra.DiagonalCosetAction`.  The fz record fz-integrate 0913-034654-15072 (GREEN, base
  e12190690, `# mods` naming `Endpoint` and `DiagonalCosetAction`) carries all five files with the bytes now
  on main.
* Census merge 4 (86df293af) listed five unwired carrier modules: three landed in wave 3, two are in wave 4.
  One census token resolves to no declaration: row 8fdc908a49c7 (definition)
  `GroupApproximation.StableWhitehead.elementaryColim_normal`.

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

## Wave 4 (launched 09-13 04:22, pre-flight at 1a033dfb3)

8 modules, 10 newly reachable files.  Module list: `$NM/rw-wave4.mods`.

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
* the five files of 8e61df1ae (root state, above), from fz-integrate 0913-034654-15072.

hull-count94's newer GREEN 0913-035614-34211 carries other `OsinLemma94AntiparallelMetric` bytes, not
landed.  Once wave 4 lands, landing them changes a root-reachable module.

### Held

| module | reason | owner |
|---|---|---|
| `NonMF.Audit.Sec3` | its bytes on main (unchanged since 03:13) lie in no GREEN record's import closure; audit-sec3's GREEN 0913-040726-62527 names it with other bytes, not landed | audit-sec3 |
| `Estimating.OsinUnboundSharedEdge` | red in root build 0913-015433-16599; its only record, 0913-022343-56095, FAILED | hull-unbound |
| `GGT.SystolicDiscMirrorFoldSteps` | queued after the wave 4 pre-flight; GREEN 0913-040558-58001 names it, bytes = main; wave 5 | ko-closed |
| `CharClass.*`, `Analysis.LIX*`, `ProblemLIXStrongAssemblyHalves` | LIX campaign files, in flight in the shared tree | LIX lanes |

Released from the wave 3 holds, all in wave 4: `OsinLemma94Pieces` (transitive build),
`LeavittMFQuotientUnitsGL` and `JacobsonComplementarySentence` (green probes since).

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
