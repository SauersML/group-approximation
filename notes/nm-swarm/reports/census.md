# census

Lane `census` of the non-MF every-line swarm (2026-09-13), target U3. The lane owns `metadata/NON_MF_SENTENCE_MAP.tsv`,
`metadata/NON_MF_SENTENCE_CENSUS.{tsv,md}`, `notes/nm-swarm/WORKLIST.md`, and both baseline files. Every census pass
runs on MSI through `$NM/census/census_merge.sh`. The script lands the result only when the merge, register,
verify-decls and verify-unconditional passes all exit 0. `--check` fails as long as any row is partial, so it does
not block landing.

## Status: merge 0913-034415 at base 5f9c16b7b, landed 88289a4ee

| status | sentences |
| --- | --- |
| `formalized` | 340 |
| `definition` | 49 |
| `structural` | 46 |
| `partial` | 26 |
| `provenance` | 19 |
| `attribution` | 18 |
| **total** | 498 |

- **Verifiers.** `--verify-unconditional` reports 377 conditional or literature-fed assignments, all accepted and 0
  new. `--verify-decls` reports 0 missing of 993 named declarations.
- **Open rows.**
  - 18 of the 26 partial rows are open on their premises. See "Open rows".
  - The other 8 are partial only because a carrier module is outside the root import closure. They regain their
    grade at the first merge after the module is wired. See "Unwired carrier modules".
- **Conditional baseline:** 135 active findings, against 132 at 86df293af. By kind: 60 `open-predicate`,
  59 `buried-conditional`, 14 `carrier-data`, 1 `conditional-data`, 1 `inlined-statement`.
  - Registered 3 lines on the Osin Lemma 9.4 carriers of rows `8aead549f1fe` and `4895f03fdf5f`, from hull-count94's
    row (70df5823f). See "register.py rules".
  - Revised 21 lines in place (see "Justification revisions"). Removed 0.

## Landings (09-13)

| merge | base | result | partial | baseline findings |
| --- | --- | --- | --- | --- |
| 0913-022302 | d6f6ccc19 | not landed: REGISTER=3, rules added | | |
| 0913-023622 | 63f147d7b | 94bb0a9f8 | 59 | 132 |
| 0913-025455 | f6985a197 | 86df293af: root-wire wave 2 restored 20 rows | 23 | 132 |
| 0913-032518 | a4fd8595c | not landed: REGISTER=3 on the hull-count94 carriers | 26 | |
| 0913-034415 | 5f9c16b7b | 88289a4ee | 26 | 135 |

- Partial rose from 23 to 26 at a4fd8595c. audit-intro's rows `be1769283b2f`, `651e122a919e` and `ec81a8c16b64`
  (tex 112, 134, 156) now cite `IntroConventionSentences`, which is not root-reachable.
- No row closed between 86df293af and 88289a4ee.

## Merge tool changes (09-13)

- **Root-reachability.** A row stays `formalized` or `definition` only when every declaration it names lives in a
  module of the `GroupApproximation` import closure, per COMMON_RULES (DONE means a closed, root-reachable carrier).
  A compiled carrier outside the closure makes the row `partial`.
  - A merged row is recomputed from the lane rows at every merge, so it recovers its grade as soon as the module is
    wired.
  - An existing map row that no lane row replaces carries the suffix
    `[census merge <sha>: DOWNGRADED from X: carrier not root-reachable at origin (...)]`, and the next merge after
    the module is wired removes it.
- **DROP overrides.** `overrides.tsv` accepts `lane<TAB>given key<TAB>DROP<TAB>declarations<TAB>reason`. The
  declarations leave that lane's row, and the row's note records the drop. A row left with no declarations is
  skipped.
- **Justification revisions.** When the premise quoted in a registered line gets closed, register.py rewrites the
  line's justification. The line keeps its (kind, declaration) key and ends with
  `[revised by the census merge at <sha>: <reason>]`. At 5f9c16b7b this rewrote 21 lines, in three groups:
  - **the hKO wall.** hzip is closed: `Systolic.zipSpurStatement` from `Systolic.zipPinchStatement`, and
    `CCKW.zipSpur_cosetComplex`. `MirrorFoldStatement` (hfold) and `SystolicInvariantCliqueStatement` (hT6) are
    still open. Owners: fff-periodic, kh-cckw, ko-closed.
  - **the hW premise.** It is closed as `HydeLodha.finitelyPresentedInfiniteSimple_closed`, but the declarations
    still bind the least-area Hull 7.1 leaves and `KotowskiOllivierStatement`.
  - **the FFF S2 producers.** 2c3c8cb40 deleted the TheoremCAssembly producers. The producers that remain bind
    `LiteratureInputs` or its open leaves.
- **register.py rules.**
  - **hKO wall.** `KotowskiOllivierClosed` and the systolic leaves are registered with the hKO text above.
  - **Hyde-Lodha chain.** These steps are registered as intermediate steps of the closed hW chain:
    `finitelyPresentedInfiniteSimpleStatement_of_{dynamics,upsilon,stabK}`, `upsilonFinitelyPresented_of_dynamics`,
    `lemmaFourSixCaseOne_of_dynamics` and `stabKFinitelyPresented_of_upsilon`. They are cited beside the closed
    endpoint, which discharges every premise with `HydeLodha.lemmaFourSixDynamics`.
  - **Osin Lemma 9.4** (hull-count94).
    - `OsinLemma94RunInput` has no producer. The planned producer is `Estimating/OsinLemma94RunProducer.lean`
      (sec5-sentences).
    - `osinLemma94Section_of_runInput` derives `OsinLemma94SectionStatement` from that input.
    - The buried premise `hmetric` of `OsinLemma94ComponentPolygons.unbound_lt` is the conclusion of
      `UnboundEstimate.unboundComponentWordPolygonsMonotone` (`#audit_closed_axioms`, root-imported), and
      `osinLemma94Section_of_runInput` supplies it.
  - **`LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial`.** Its premise `hEL` is
    `thm:full-defect-ring` at `L_k(1,d)`. The sibling carrier `manuscriptSentence_bothInclusionsPrinted`
    (`#audit_closed_axioms`) discharges it in the same row. This is internal proof modularization.
  - **`HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`.** Its premise
    `D.IsHyperbolicallyEmbedded` is the definition (DGO Definition 4.25) inside Hull Lemma 5.8's printed
    hypothesis. The sibling carrier `printedHullLemma58` takes it from that hypothesis.
- **Landing.**
  - The script lands as lane census and checks the MSI master with `ssh -O check`.
  - The passes run detached on the node and are polled for a sentinel.
  - `notes/nm-swarm/WORKLIST.md` lands together with the map, the register and the census.

## Overrides in force

- **Re-keys.** In both rows the note quotes the sentence, and the text match lost only on margin:
  - jacobson `LINE:1147` goes to `b6d1590be7ab`, the GHW / Kazhdan-subgroup sentence;
  - sec3-sentences `LINE:837` goes to `bd35898b630c` ("Since r=vwr+fr ...").
- **Retirements.** These follow the lead's ruling of 2026-09-13 on debt-conditional groups B and C (baseline line
  numbers at 87790c4fa). All 19 lines were removed at 94bb0a9f8.
  - sec5-sentences `LINE:1636`, `1644`, `1662`, `1665` and `1698` drop their historical quasi-geodesic and unbounded
    Lemma 4.4 carriers.
  - hull-respell `LINE:1636`/`1644` drop the three `_of_quasiGeodesicLeaves` declarations, and `LINE:1675` drops
    `osin24HullStep_of_boundedLeaves`.
  - The replacements are the four-leaf carriers already landed: sec5-sentences rows 27 to 30,
    `printedHullTheorem*_of_fourLeaves` from nm-endpoints, and `fournierFacioQuotient_of_fourLeaves`.

## Rows skipped

- **dgo-analytic `LINE:1688`: ambiguous.** The two candidates are `d8d9d495865d` (line 1690, score 0.29) and
  `8e8d5f3f8be0` (line 1687, score 0.17).
  - The note describes the DGO half of `f2bf6328169e` (tex 1725).
  - The census does not re-key it. The row is graded partial, and the union rule would hold `f2bf6328169e` at
    partial.
  - Owner dgo-analytic: re-grade the row, or replace it with `SUPERSEDES`.
- **hull-respell `LINE:1636` and `LINE:1644`.** The DROP overrides removed every declaration, so the rows are
  skipped.

## Unwired carrier modules (5 at 5f9c16b7b, 8 rows)

| module | rows (tex line) | wire queue line |
| --- | --- | --- |
| `Manuscript.NonMFSentences.IntroConventionSentences` | `be1769283b2f`@112, `651e122a919e`@134, `ec81a8c16b64`@156 | audit-intro 798be51a3 |
| `Manuscript.NonMFSentences.LeavittMFQuotientUnitsGL` | `dcf6fa4be4de`@1298, `7916c8696def`@1307 | leavitt-units 4f629158e |
| `Manuscript.NonMFSentences.FullDefectPairLeavitt` | `a4b5b1a0504a`@1008 | baseline-debt 296386753 |
| `Sofic.StrongConvergenceMFSubsingleton` | `b1b04e376fe7`@99 | baseline-debt 296386753 |
| `Manuscript.OneSidedMFRadical.JacobsonComplementarySentence` | `c149d33e8f7e`@1145 | none |

- **No path to the root:** `JacobsonComplementarySentence`. It has no importer and no wire-queue line.
  - The module is closed (`#audit_closed_axioms`, no sorry). It imports only `FullDefectRingEJZUnconditional` and
    `JacobsonFiniteMatrices`.
  - It holds the only copy of `JacobsonSymbol.manuscriptSentence_twoResultsComplementary`.
  - It needs a root import and a green probe record. Owners: jacobson and root-wire.
- **`IntroConventionSentences`:** its only importer, `NonMF.Audit.Intro`, has no importer itself, so the module
  needs its own queue line to be wired.

## Open rows at 88289a4ee (26 partial, by owner)

The keys are sentence keys; `notes/nm-swarm/WORKLIST.md` has the full sentences and declarations.

| owner | rows | keys @ tex line |
| --- | --- | --- |
| nm-endpoints | 8 | `a16637da7249`@66, `0f22bdbc4184`@285, `dce7a9ff4e83`@291, `8aead549f1fe` `4895f03fdf5f`@1637, `2f55113239ce`@1651, `7b1fa3182135` `8b1ec28a0e73`@1719 |
| cite-hull | 4 | `a9dd4b90e479`@1629, `bcc99703f838`@1644, `2d1cd22e5f49` `2f997e5af4e6`@1659 |
| sec2-sentences | 4 | `b1b04e376fe7`@99, `be1769283b2f`@112, `651e122a919e`@134, `ec81a8c16b64`@156 |
| cite-hull+kh-ejz+nm-endpoints | 2 | `8097c371f35d` `dab2f2bfe084`@1675 |
| ghw-assembly | 2 | `b6d1590be7ab` `3009704fef89`@1145 |
| leavitt-units | 2 | `dcf6fa4be4de`@1298, `7916c8696def`@1307 |
| sec5-sentences | 2 | `721da4c14d11`@1697, `92115dd7edef`@1725 |
| audit-sec3 | 1 | `a4b5b1a0504a`@1008 |
| jacobson | 1 | `c149d33e8f7e`@1145 |

- **Open only through root reachability** (8 rows): sec2-sentences 4, leavitt-units 2, audit-sec3 1, jacobson 1.
- **Open on premises** (18 rows): nm-endpoints 8, cite-hull 4, cite-hull+kh-ejz+nm-endpoints 2, ghw-assembly 2,
  sec5-sentences 2.
  - The endpoint and Hull rows sit over the least-area Hull 7.1 leaves (hgreendlinger, hbridge).
  - The Fournier-Facio rows also sit over hKO (hfold, hT6).
  - `8aead549f1fe` and `4895f03fdf5f` also carry the Osin Lemma 9.4 run input.

## Row files

- `metadata/nm-census-rows/hull-count94.tsv` is on origin (70df5823f). It was merged at 5f9c16b7b into
  `8aead549f1fe` and `4895f03fdf5f`, which stay partial.

## Next

- Re-merge when root-wire wires any module in the table above or a lane lands rows, and at least every ~2 h.
- jacobson / root-wire: give `JacobsonComplementarySentence` a queue line.
- dgo-analytic: re-grade `LINE:1688` or add `SUPERSEDES`.
