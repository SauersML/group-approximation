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
* `rw/rwtool.py <sha> census`: census tokens resolved to declaring files; carriers whose files are not
  root-reachable.

## 09-13 root state (origin/main ff0bb5026, 01:52)

* Root: 4672 GroupApproximation import lines, all before the module docstring (OK); no missing
  module, no duplicate line; closure 6038 modules; 0 dangling imports inside it.
* 421 modules on main are not reachable from the root.
* Census: 7 carrier modules unreachable, all in wave 1: `Algebra.PreusserSandwichExchange`,
  `NonMF.TorsionFreeAlgebraSentencesClosed`, `NonMF.TorsionFreeSectionSentencesLeastArea`,
  `NonMFSentences.AmenableTraceSentencesB`, `NonMFSentences.BinaryExampleSentences`,
  `NonMFSentences.IntroSentences`, `NonMFSentences.KorchaginFullSequenceSentence`.
  One census token resolves to no declaration: row 8fdc908a49c7 (definition)
  `GroupApproximation.StableWhitehead.elementaryColim_normal`.

## Wave 1 (launched 09-13 01:54, root build 0913-015433-16599, base c737ec92d)

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

`TorsionFreeSectionAssembly` (initial queue) is already rooted.  `SystolicDiscZip` is not on main; the
module on main is `SystolicDiscZipFold`.

### Held

| module | reason | owner |
|---|---|---|
| `GGT.SystolicProjectionClique` | probe 0913-013608 FAILED; landed unverified 3cf9bd845 | kh-cckw |
| `NonMFSentences.LeavittMFQuotientBothInclusions` | probe 0913-014841 pending | leavitt-units |
| `NonMFSentences.LeavittMFQuotientDiagonalSentence` | probe 0913-014841 pending | leavitt-units |
| `HydeLodha.QTwoLemmaFourSixGenerators` | probe 0913-013413 FAILED on it (Statements and InfiniteSimpleClosed compiled; they do not import it) | simple-group |
| `CharClass.*`, `Analysis.LIX*`, `ProblemLIXStrongAssemblyHalves` | LIX campaign files, in flight in the shared tree | LIX lanes |

Without a current probe record, the root build is the evidence for: `KotowskiOllivierLeaves`,
`TorsionFreeKOLeaves` (lead, unverified 3cf9bd845); the 09-12 landings restored at 3f71a3a50
(PreusserSandwichExchange and the other census carriers); the Planar/Surgery/OsinAppendixEuler chains.

## Stale notes superseded

* wire-queue line 318 "GHBHyperbolicDiscCounts waits on red Filling/Counts": Counts and Filling are
  green at 4c12845a1 (systolic-counts report).
* `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`: renamed in
  6a5f25704; both are in wave 1.
* Wave 4 of 09-12 (40 modules) never landed; its modules are in wave 1.
