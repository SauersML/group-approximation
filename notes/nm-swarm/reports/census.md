# census

Lane `census` of the non-MF every-line swarm (2026-09-13), target U3. The lane owns `metadata/NON_MF_SENTENCE_MAP.tsv`,
`metadata/NON_MF_SENTENCE_CENSUS.{tsv,md}`, `notes/nm-swarm/WORKLIST.md`, and both baseline files. Every census pass
runs on MSI through `$NM/census/census_merge.sh`. The script lands the result only when the merge, register,
verify-decls and verify-unconditional passes all exit 0. `--check` fails as long as any row is partial, so it does
not block landing.

## Status: merge 0913-023622 at base 63f147d7b, landed 94bb0a9f8

| status | sentences |
| --- | --- |
| `formalized` | 306 |
| `partial` | 59 |
| `definition` | 50 |
| `structural` | 46 |
| `provenance` | 19 |
| `attribution` | 18 |
| **total** | 498 |

- **Verifiers.** `--verify-unconditional` reports 371 conditional or literature-fed assignments, all accepted and 0
  new. `--verify-decls` reports 0 missing of 960 named declarations.
- **Root reachability.** 41 rows that their lanes graded `formalized` or `definition` are partial only because a
  carrier module is outside the root import closure (21 merged rows, 20 existing rows). They regain their grade at
  the first merge after root-wire wires the modules; see "Unwired carrier modules".
- **Conditional baseline:** 132 active findings, against 102 at 87790c4fa.
  - Removed 51 stale lines on 43 declarations: 27 `conditional-debt`, 9 `carrier-debt`, 7 `buried-conditional`,
    5 `open-predicate`, 2 `carrier-data` and 1 `inlined-statement`.
    - The 27 are every `conditional-debt` line, which debt-conditional predicted would go stale once 2c3c8cb40
      deleted the TheoremC producers.
    - The removed lines include the 19 lead-ruled retirements below.
  - Registered 81 lines on 49 declarations. 10 of these declarations are re-kinds of removed ones; the other 39
    were not in the baseline before.
    - By kind: 34 `open-predicate`, 33 `buried-conditional`, 12 `carrier-data`, 1 `conditional-data`,
      1 `inlined-statement`.
    - By premise:
      - 32 over the least-area Hull 7.1 leaves;
      - 22 `KotowskiOllivierStatement` feeding Fournier-Facio's G_0;
      - 11 printed statements named as vocabulary;
      - 10 on the hKO systolic leaves;
      - 3 on the FFF S2 paragraph;
      - 1 Lemma 4.4 one-step statement;
      - 2 internal (see "register.py rules").

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
- **register.py rules.**
  - `KotowskiOllivierClosed` and the systolic leaves (`ZipSpurStatement`, `ZipPinchStatement`,
    `MirrorFoldStatement`, `SystolicInvariantCliqueStatement`) are registered as the hKO wall. Owners: kh-torsion,
    fff-periodic, kh-cckw, ko-closed.
  - Plain `HullOneStepStatement` is registered with the Hull 7.1 one-step statements.
  - `LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial`: its premise `hEL` is
    `thm:full-defect-ring` at `L_k(1,d)`. The sibling carrier `manuscriptSentence_bothInclusionsPrinted`
    (`#audit_closed_axioms`) discharges it in the same row with
    `FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics`. This is internal
    proof modularization, the same shape as baseline line 171.
  - `HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`: its premise
    `D.IsHyperbolicallyEmbedded` is the definition (DGO Definition 4.25) inside Hull Lemma 5.8's printed hypothesis.
    The sibling carrier `printedHullLemma58` (`#audit_closed_axioms`) takes it from that hypothesis.
- **Worklist owners** follow the 09-13 roster.
- **Landing.**
  - The script lands as lane census and checks the MSI master with `ssh -O check`.
  - The passes run detached on the node and are polled for a sentinel.
  - `notes/nm-swarm/WORKLIST.md` lands together with the map, the register and the census.

## Overrides in force

- **Re-keys.** In both rows the note quotes the sentence, and the text match lost only on margin:
  - jacobson `LINE:1147` goes to `b6d1590be7ab`, the GHW / Kazhdan-subgroup sentence;
  - sec3-sentences `LINE:837` goes to `bd35898b630c` ("Since r=vwr+fr ...").
- **Retirements.** These follow the lead's ruling of 2026-09-13 on debt-conditional groups B and C (baseline lines
  numbered at 87790c4fa). All 19 lines are removed at 94bb0a9f8.
  - sec5-sentences `LINE:1636`, `1644`, `1662`, `1665` and `1698` drop their historical quasi-geodesic and unbounded
    Lemma 4.4 carriers. This retires lines 246, 255, 256, 261, 262, 270, 271, 274, 275, 292 and 293.
  - hull-respell `LINE:1636`/`1644` drop the three `_of_quasiGeodesicLeaves` declarations, and `LINE:1675` drops
    `osin24HullStep_of_boundedLeaves`. This retires lines 239 to 244, 280 and 282.
  - The replacements are the four-leaf carriers already landed: sec5-sentences rows 27 to 30,
    `printedHullTheorem*_of_fourLeaves` from nm-endpoints, and `fournierFacioQuotient_of_fourLeaves`.

## Rows skipped or waiting

- **dgo-analytic `LINE:1688`: ambiguous.** The two candidates are `d8d9d495865d` (line 1690, score 0.29) and
  `8e8d5f3f8be0` (line 1687, score 0.17).
  - The note describes the DGO half of `f2bf6328169e` (tex 1725), landed at 14914dfd2 and 0cdf0b924.
  - The census does not re-key it: the row is graded partial, and the union rule would hold `f2bf6328169e` at
    partial.
  - Owner dgo-analytic: re-grade the row, or replace it with `SUPERSEDES`.
- **hull-respell `LINE:1636` and `LINE:1644`:** the DROP overrides removed every declaration, so the rows are
  skipped.

## Unwired carrier modules (33 at 63f147d7b)

- **In root-wire wave 2** (launched 02:30, base 6292a1395), 25 modules. Wave 2 also brings in
  `OneSidedMFRadical.JacobsonKernelFinitary` and `JacobsonBlockAction` through `JacobsonRankTwoCarrier`.
  - `Algebra.PreusserSandwichExchange`
  - `GGT`: `SystolicDiscZip`, `SystolicDiscZipFold`
  - `Kazhdan`: `GHBLatticeRouteKazhdan`, `GHWCharP`, `GHWCharPClosed`, `KotowskiOllivierClosed`
  - `Manuscript.NonMF`: `HullCitationSentences`, `HullTheorem312Lemma58`, `OsinCitedSentencesClosed`,
    `TheoremCAssemblyKOLeaves`, `TorsionFreeAlgebraSentencesClosed`, `TorsionFreeDefectNormalClosure`,
    `TorsionFreeFourLeaves`, `TorsionFreeSectionSentencesFourLeaves`, `TorsionFreeSectionSentencesLeastArea`
  - `Manuscript.NonMFSentences`: `AmenableTraceSentencesB`, `BinaryExampleSentences`, `EJZCitationSentences`,
    `IntroSentences`, `LeavittMFQuotientBothInclusions`, `LeavittMFQuotientDiagonalSentence`,
    `LimitingTraceTrivialCharacterSentence`
  - `Manuscript.OneSidedMFRadical`: `HSVanishesProducers`, `JacobsonRankTwoCarrier`
- **In the wire queue after the wave-2 cut**, 5 modules:
  - `GroupTheory.HydeLodha.QTwoLemmaFourSixDynamics`
  - `NonMF.NaiveFreeProductPropertyOfAcylindricallyHyperbolic`
  - `NonMFSentences.FullDefectPairLeavitt`
  - `NonMFSentences.LeavittMFQuotientUnitsGL`
  - `Sofic.StrongConvergenceMFSubsingleton`
- **No path to the root:** `Manuscript.OneSidedMFRadical.JacobsonComplementarySentence`. It has no importer, no
  wire-queue line and no green probe record, so row `c149d33e8f7e` stays partial. Owners: jacobson and root-wire.
- **Not yet cited:** kh-torsion landed `GGT.SystolicDiscZipPinch.zipPinchStatement` (d74b84054, lexically
  sorry-free), which closes the pinch case of hzip. Nothing imports the module, and the kh-torsion row `LINE:1675`
  does not cite it yet.

## census-notes items

- `07642b10d3ee` / `330d435b12e2` (sec2): origin already cites `AffineHNNBase.manuscriptSentence_ascendingHNNMatrixRealization`,
  `realization_injective`, `range_realization` and `NonMFSentences.reductionHom`. The grade now depends only on root
  wiring.
- tex 372-379 (block-sum family): in the census as `07de7e8a943a` and `8e54f4138ac7`.
- `a4b5b1a0504a` / `34366ed3b6a0` (sec3): both rows now cite `FullDefectCornerRemark`. The finding on
  `manuscriptSentence_cornerPassesUp` is stale at 63f147d7b and has been removed.
- rescue-lix Palomar note: not census work.

## Row files in the shared tree but not on origin (checked at 90e5780b1)

- `metadata/nm-census-rows/hull-count94.tsv` (`LINE:1636 partial`, OsinLemma94 run-input carriers): owned by
  hull-count94. The merge reads rows only from origin, so it cannot see this file.
- `metadata/nm-census-rows/lix-descent.tsv`: LIX campaign, outside the manuscript.

## Open rows at 94bb0a9f8 (59 partial, by owner)

The keys are sentence keys, and the full sentences and declarations are in `notes/nm-swarm/WORKLIST.md`.

| owner | rows | keys @ tex line |
| --- | --- | --- |
| audit-sec3 | 20 | `0939d33e1ff4`@936, `a4b5b1a0504a`@1008, `2ff180315a15` `98115b8e2580`@1163, `a71f65809e0b` `e47b80780566`@1170, `2bf4b5aca1b4`@1178, `7a20735318a1` `9085fad2968e` `d38df1795c78` `bfd4d3ceba5a` `8ed259b70c4a`@1185, `ecb74cabf11a`@1197, `c41bad22d29b`@1475, `177456a78260` `dba28fb94e6d` `91502a70ae59` `24b5330b38b0`@1501, `c48c7da870a2` `8c17c33ec225`@1608 |
| nm-endpoints | 8 | `a16637da7249`@66, `0f22bdbc4184`@285, `dce7a9ff4e83`@291, `8aead549f1fe` `4895f03fdf5f`@1637, `2f55113239ce`@1651, `7b1fa3182135` `8b1ec28a0e73`@1719 |
| cite-hull | 5 | `a9dd4b90e479`@1629, `bcc99703f838`@1644, `c650b0a20b89` `2d1cd22e5f49` `2f997e5af4e6`@1659 |
| jacobson | 5 | `0a08ffd095d6` `d5e56b196927` `7c69447e3d41` `754a868fc8f5`@1122, `c149d33e8f7e`@1145 |
| audit-intro | 4 | `07de7e8a943a`@372, `c36b6021a802`@572, `47c65457b63c` `4cd99c2ee1cb`@717 |
| leavitt-units | 4 | `dcf6fa4be4de`@1298, `7916c8696def` `4321530b3fec` `f6962254d259`@1307 |
| sec2-sentences | 4 | `b1b04e376fe7`@99, `10e027681ba5` `f2a05ccf5990`@122, `6edef6dc2d68`@298 |
| sec5-sentences | 4 | `721da4c14d11`@1697, `d29816e1de56`@1705, `92115dd7edef` `f2bf6328169e`@1725 |
| ghw-assembly | 2 | `b6d1590be7ab` `3009704fef89`@1145 |
| cite-hull+kh-ejz+nm-endpoints | 2 | `8097c371f35d` `dab2f2bfe084`@1675 |
| sec2-sentences+hs-vanishes | 1 | `61827aea7807`@187 |

## Next

- Re-merge now, to pick up simple-group's hW rows (b4271455d).
- Then re-merge after root-wire wave 2 lands, and at least every ~2 h.
