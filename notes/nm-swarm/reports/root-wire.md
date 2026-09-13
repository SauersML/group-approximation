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
  root closure.
* Evidence: the last `$NM/lanes/<lane>.green.*` record naming a module, and the lane reports.  A module
  whose last probe failed, or whose import closure contains one, is held.
* Changed bytes: every file in the new closure that changed on main since the previous root build's
  base must equal its newest GREEN record (`rw/rwevidence.sh`, `git cat-file -e` before any md5).
* `rw/rwtool.py <sha> census`: census tokens resolved to declaring files; carriers whose files are not
  root-reachable.

## 09-13 root state (origin/main 6292a1395, 02:25)

* Root: 4672 GroupApproximation import lines, all before the module docstring (OK); no missing
  module, no duplicate line; closure 6038 modules; 0 dangling imports inside it.
* 449 modules on main are not reachable from the root (421 at ff0bb5026).
* Census: 7 carrier modules unreachable, all in waves 1 and 2: `Algebra.PreusserSandwichExchange`,
  `NonMF.TorsionFreeAlgebraSentencesClosed`, `NonMF.TorsionFreeSectionSentencesLeastArea`,
  `NonMFSentences.AmenableTraceSentencesB`, `NonMFSentences.BinaryExampleSentences`,
  `NonMFSentences.IntroSentences`, `NonMFSentences.KorchaginFullSequenceSentence`.
  One census token resolves to no declaration: row 8fdc908a49c7 (definition)
  `GroupApproximation.StableWhitehead.elementaryColim_normal`.

## Wave 1 (launched 09-13 01:54, root build 0913-015433-16599, base c737ec92d): RED

108 modules, 123 newly reachable files: the initial queue, every non-LIX queue line, landed campaign
modules from `landed.log`, the census carriers, and the 01:34–01:48 green landings (SystolicDiscZipFold
kh-torsion 0913-013751, GHWCharPClosed ghw-assembly 0913-013742, TheoremCAssemblyKOLeaves
theoremc-retire 0913-013843, TorsionFreeSectionSentencesFourLeaves sec5 0913-014453, HSVanishesProducers
and IntroLimitingTraceSentence hs-vanishes 0913-014626, LimitingTraceTrivialCharacterSentence sec2
0913-014750).  Module list: `$NM/rw-wave1.mods`.

Pre-flight at ff0bb5026: no dangling import, no lexical sorry, no cycle.  dupcheck predicts one
collision, `is`, which is a false positive: it is docstring prose ("theorem is proved in the
repository ...") in `NonMFSentences/EJZCitationSentences.lean`, of the same shape as lines already in
the root closure.

Result: ROOT FAILED rc=1; nothing landed.  14812 of 14816 targets built.  The only failing module is
`GGT.VanKampen.Estimating.OsinUnboundSharedEdge` (hull-unbound; landed 707c06d58, edited b52365364,
no probe record in `$NM/lanes`, imported by nothing on main):

* `:147:0` deterministic timeout at `whnf` (200000 heartbeats);
* `:227:8` and `:251:10` failed to synthesize instance of type class.

## Wave 2 (launched 09-13 02:30, base 6292a1395)

116 modules, 135 newly reachable files: wave 1 without `OsinUnboundSharedEdge`, plus the queue entries
after the 01:55 cut and the modules released from the wave-1 hold table.  Module list: `$NM/rw-wave2.mods`.

| added module | evidence (bytes on 6292a1395 = record) | owner |
|---|---|---|
| `NonMF.HullTheorem312Lemma58` | GREEN 0913-015651-30488 (landed e182ac440) | cite-hull |
| `NonMF.TorsionFreeDefectNormalClosure` | GREEN 0913-015553-23837 (landed 8a7de88a6) | audit-sec5 |
| `NonMF.Audit.Sec5` | GREEN 0913-015553-23837 (landed 8a7de88a6) | audit-sec5 |
| `NonMFSentences.LeavittMFQuotientBothInclusions` | GREEN 0913-014841-85842 | leavitt-units |
| `NonMFSentences.LeavittMFQuotientDiagonalSentence` | GREEN 0913-014841-85842 | leavitt-units |
| `GGT.SystolicProjectionClique` | GREEN 0913-015305-10857, again in 0913-020656-77896 | kh-cckw |
| `GGT.SystolicTriangleCondition` | GREEN 0913-015305-10857, again in 0913-020656-77896 | kh-cckw |
| `GGT.SystolicDiscZip` | GREEN 0913-015959-45107 | kh-torsion |
| `HydeLodha.QTwoLemmaFourSixGenerators` | GREEN 0913-015349-13908, again in 0913-021204-99418 | simple-group |

Pre-flight at 6292a1395: no dangling import, no lexical sorry, no cycle; dupcheck predicts only the
`is` false positive.  Of the 32 Lean files changed on main since c737ec92d, 12 lie in the new closure
(9 newly reached, 3 already rooted), and each equals its newest GREEN record.  The newly reached ones
include `QTwoLemmaFourSixAssembly` (simple-group 0913-021204) and `QTwoLemmaFourSixTransfer` (kh-ejz
0913-020001), reached through `FinitelyPresentedInfiniteSimpleClosed`.  The changed files with no record
(`GHWEntries`, `IntegerGridFinite`, `HullSCLemma51LetterPullbackCutFaces`, `Pestov91.*`, `ThompsonOre.*`,
`TypeA2.GeoFStabilizer`) are all outside the new closure.

### Held

| module | reason | owner |
|---|---|---|
| `GGT.VanKampen.Estimating.OsinUnboundSharedEdge` | red in root build 0913-015433-16599 (above) | hull-unbound |
| `CharClass.*`, `Analysis.LIX*`, `ProblemLIXStrongAssemblyHalves` | LIX campaign files, in flight in the shared tree | LIX lanes |

Released from the wave-1 hold table into wave 2: `SystolicProjectionClique` (probe 0913-013608 had
failed; kh-cckw landed green bytes), the two `LeavittMFQuotient` modules (probe 0913-014841 GREEN),
`QTwoLemmaFourSixGenerators` (probe 0913-015349 GREEN).

Without a current probe record, the root build is the evidence for: `KotowskiOllivierLeaves`,
`TorsionFreeKOLeaves` (lead, unverified 3cf9bd845); the 09-12 landings restored at 3f71a3a50
(PreusserSandwichExchange and the other census carriers); the Planar/Surgery/OsinAppendixEuler chains.
Wave 1 compiled all of them at c737ec92d.

## Stale notes superseded

* wire-queue line 318 "GHBHyperbolicDiscCounts waits on red Filling/Counts": Counts and Filling are
  green at 4c12845a1 (systolic-counts report).
* `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`: renamed in
  6a5f25704; both are in wave 1.
* Wave 4 of 09-12 (40 modules) never landed; its modules are in wave 1.
* root-wire's 01:58 message to main said `SystolicProjectionClique` was held on red bytes on main;
  kh-cckw's green bytes landed minutes later, and the module is in wave 2.
