# census

Lane `census` of the non-MF every-line swarm (2026-09-13), target U3. The lane owns `metadata/NON_MF_SENTENCE_MAP.tsv`,
`metadata/NON_MF_SENTENCE_CENSUS.{tsv,md}`, `notes/nm-swarm/WORKLIST.md`, and both baseline files. Every census pass
runs on MSI through `$NM/census/census_merge.sh`. The script lands the result only when the merge, write, register,
verify-decls and verify-unconditional passes all exit 0. `--check` fails as long as any row is partial, so it does
not block landing.

## Status: merge 0913-141044 at base 36ff632cd, landed 6457b79e5

| status | sentences |
| --- | --- |
| `formalized` | 347 |
| `definition` | 53 |
| `structural` | 46 |
| `provenance` | 19 |
| `attribution` | 18 |
| `partial` | 15 |
| **total** | 498 |

- **Verifiers.** `--verify-unconditional`, with the verifier fixed at 736f7ea44, reports 380 conditional or
  literature-fed assignments, all accepted and 0 new. `--verify-decls` reports 0 missing of 1229 named declarations.
- **Conditional baseline:** 244 active findings, against 146 at d0aba6104.
  - Merge 19 removed 17 stale lines, revised 102 in place and registered 115 new ones.
  - By kind: 109 `buried-conditional`, 106 `open-predicate`, 22 `carrier-data`, 4 `conditional-data`, 3
    `inlined-statement`.
- **Closed at merge 19:** `3009704fef89` (tex 1155) and `92115dd7edef` (tex 1728, DGO 2.35) went from `partial` to
  `formalized`.
- **Open rows:** 15 partial. See "Open rows".
- **CI.** The "Sentence-level census" step has not yet run against this baseline. `build-non-mf-pdf.yml` runs only
  after a successful push run of Lean Prover CI. The last eight of those, from 6457b79e5 through 538afe1ed, were
  cancelled, and the PDF workflow skipped every run.

## Landings (09-13)

| merge | base | result | partial | baseline findings |
| --- | --- | --- | --- | --- |
| 0913-022302 | d6f6ccc19 | not landed: REGISTER=3, rules added | | |
| 0913-023622 | 63f147d7b | 94bb0a9f8 | 59 | 132 |
| 0913-025455 | f6985a197 | 86df293af: root-wire wave 2 restored 20 rows | 23 | 132 |
| 0913-032518 | a4fd8595c | not landed: REGISTER=3 on the hull-count94 carriers | 26 | |
| 0913-034415 | 5f9c16b7b | 88289a4ee | 26 | 135 |
| 0913-042746 | 395b3c31c | 39dd43b39 | 22 | 135 |
| 0913-043826 | cba3ce8ba | a3e35aece | 26 | 135 |
| 0913-044759 | df84b2475 | a21cc0c19 | 27 | 135 |
| 0913-050040 | 245a1c0c2 | 6fd3d7a55 | 23 | 135 |
| 0913-053204 | e32bac3f3 | not landed: REGISTER=3 (2 unclassified), VERIFY_UNCOND=1 | 18 | |
| 0913-064842 | 45358bab7 | dump only, no landing | 17 | |
| 0913-074521 | 77c9de1d2 | not landed: REGISTER=3 (6 unclassified) | 18 | |
| 0913-085330 | 045b5f849 | 9b413742b | 18 | 153 |
| 0913-090435 | d0a41c1da | 9a13b22c9: dgo-analytic SUPERSEDES row merged in, no register change | 18 | 153 |
| 0913-091312 | 736bfe261 | de0c922ef: root wiring at 559636b4a restored `b6d1590be7ab` | 17 | 153 |
| 0913-094419 | 020a1d43e | not landed: REGISTER=1, a variable clash in census's new clause pass | 17 | |
| 0913-101444 | 8bff272fa | d0aba6104 | 17 | 146 |
| 0913-112535 | e5982243f | not landed: REGISTER=3, the two `hhard` inline statements unclassified | | |
| 0913-141044 | 36ff632cd | 6457b79e5: re-registered against the verifier fix 736f7ea44 | 15 | 244 |

## Walls of sec:torsion-free (at 36ff632cd)

Three of the four walls are closed.

- **hKO.** `TheoremC.KotowskiOllivierStatement` is closed by `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`
  (`#audit_closed_axioms`, root-imported, f65f99f17) over `Systolic.mirrorFoldPinched` (426813b24).
- **hbridge.** `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` is closed by
  `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` (`#audit_closed_axioms`, root-imported, 18682110d).
- **hW.** `FinitelyPresentedInfiniteSimpleStatement` (Hyde-Lodha) is closed by
  `HydeLodha.finitelyPresentedInfiniteSimple_closed` (`#audit_closed_axioms`).

The residual is **hgreendlinger** (`RelativeGreendlingerQuasiGeodesicLeastAreaStatement`), not yet produced. Its
producers bind Osin's Lemma 9.4 (`OsinLemma94SectionStatement`) with the pocket inputs, Osin's Lemma 9.7, or the
historical `RelativeGreendlingerQuasiGeodesicStatement`.

### Lemma 9.4

`osinLemma94Section_of_residuals` (`#audit_axioms`, OsinLemma94SectionResiduals, 4002b9371) applies
`osinLemma94Section_of_planarPieces` (80790fad1) to three closed pieces and takes the other two as hypotheses.

| piece | state | owner |
| --- | --- | --- |
| metric half | closed: `osinLemma94AntiparallelMetric` (e3da1ba60) | |
| `OsinLemma94PolygonRealizationInput` | closed: `osinLemma94PolygonRealizationInput` (4002b9371) over the partition `osinLemma94PolygonPartitionInput` (746028b24) | hull-unbound, ghw-assembly |
| `OsinLemma94CaseTwoInput` | closed: `osinLemma94CaseTwoInput` (e0e94015d) over `separatedCornerInsertionInput` (619b70139) | sec5-sentences |
| `OsinLemma94PolygonCountInput` (`hcount`) | open: reduces to the side budget `OsinLemma94PolygonSideBudgetInput` | hull-count94, sec5-sentences |
| `OsinLemma94CaseOneInput` (`hone`) | open: a producer and a walk that no declaration composes | theoremc-retire, ko-closed, jacobson |

- **Realization pieces.** All four pieces of `osinLemma94PolygonRealizationInput_of_pieces` (1130c8dbc) are produced:
  - cutting chains: `osinLemma94CuttingChainsInput_of_pieces` (108236c25), from `chainRespellInput_of_pieces` over
    `cornerInsertionInput` (f7538e223) and `pendantPathRemovalInput` (61c2ade8e), and from `quasiGeodesicRespellInput`
    (bbb8585ab);
  - cell arcs: `osinLemma94CellArcsInput_holds` (5e5a98049);
  - boundary arcs: `osinLemma94BoundaryArcsInput` (`#audit_closed_axioms`, 1b453429f);
  - partition: `osinLemma94PolygonPartitionInput` (`#audit_closed_axioms`, 746028b24).
- **Count.** K is chosen after eps since 9f8779c4e (ruled F1). The side budget is still over-strong as stated. A
  G-face that reads a value-one subword of the boundary, such as a bubble on a spur of a section, is a polygon with no
  (A1) side, and there can be arbitrarily many of them with n = 1.
  - The ruled patch counts classes over the polygons with an (A1) side. A class is a maximal run of consecutive cell
    sides whose gaps have value one. The patch respells the covering half over the class word, with
    L = 24 eps + 2 (K + 24) ceil((c + 2) / lambda). It is not landed.
  - The (A3) short sides number at most 2 eps |M| (`sum_card_shortSides_le`, 4b6dd3cd8, not root-reachable).
- **Case 1.** `osinLemma94CaseOneInput_of_walk` (5be5cb6fc, not root-reachable) and `osinLemma94CaseOneWalk`
  (eb9010962, root-imported) are not composed.
  - ghw-charp2's census patch 10(f), not landed, adds `hkind` to `osinLemma94CaseOne_false_of_walk` and deletes
    `_of_walk`.
  - The one-cell connector pairs then stay the same-cell binder `OsinLemma94CaseOneSameCellStatement` (3292f7a20).
  - A pocket with no relator cell is refuted by `false_of_cellFree_pocket_X` and `_Y` (ea9016135, not
    root-reachable). A pocket with a relator cell needs Osin's loop case under `OsinLemma97Below`.
- **Root imports.** e0dcf8b99 root-imports OsinLemma94CornerInsertion, CuttingChains, QuasiGeodesicRespell, CellArcs,
  BoundaryArcs, PolygonPartition, PolygonMaximal, SectionResiduals, CaseTwo, SeparatedInsertion and
  SeparatedInsertionProof, and HullLemma35Printed and HullLemma35Closed. OsinUnboundCaseOneRun,
  OsinLemma94OneCellValue and OsinLemma94ShortSides are outside the import closure at 36ff632cd.
- **Route refuted.**
  - `Embedded.FaceSetEarStatement` and `FaceSetEarDataStatement` are false (`not_faceSetEarStatement`,
    `not_faceSetEarDataStatement`, 9dda53a05).
  - So is `RegionShellingStatement` (`not_regionShellingStatement`, 3f6eaff76).
  - A baseline line that binds one of them is graded "route refuted; W1 (a) is on the ofPlanar carrier", not open.
- **Forms over hgreendlinger alone.** They are in `TorsionFreeGreendlingerLeaf`, `TorsionFreeGreendlingerSentences`,
  `TorsionFreeGreendlingerForms`, `HullSCGreendlingerForms`, `TheoremCAssemblyGreendlingerLeaf` and `HullCorollary74`.
  All six are root-imported at 559636b4a.

## The verifier fix at 736f7ea44

systolic-counts fixed both defects census found in `scripts/check_non_mf_unconditional.py`.

- **Partial namespace paths.** `resolve_written_name` tries each namespace prefix, as Lean does, so
  `kotowskiOllivier_closed` now produces `KotowskiOllivierStatement`. Merge 19 revised the lines that quoted the false
  red and the leads that named hKO as the open premise.
- **In-place constructions.** `in_place_heads` reads `have`/`let` bindings and anonymous constructors. Merge 19
  removed the two CutLift lines (`HullSC.cutLiftOutcome`, `HullSC.CutLift.toCutMove`) as stale.
- **New findings.** The old resolver dropped the partial path of `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`,
  so the `TheoremC.LiteratureInputs` producers over it, `FournierFacioParagraph`, `HullOneStepStatement`,
  `HullTowerStatementGeneral` and the Printed* carriers counted as discharged. They now count as conditional over
  hgreendlinger, and merge 19 registers them.
  - Against 736f7ea44, the old baseline gave 174 new findings on 115 (kind, declaration) pairs: 134 `open-predicate`,
    19 `carrier-data`, 16 `buried-conditional`, 3 `conditional-data` and 2 `inlined-statement`.
  - 119 of the 174, on 86 declarations, bind hgreendlinger, and 10 more bind `FournierFacioParagraph`.
  - The 115 new lines: 91 `open-predicate`, 14 `carrier-data`, 6 `buried-conditional`, 2 `conditional-data` and 2
    `inlined-statement`.
- **Other stale lines.** The remaining 15 of the 17 no longer produce a finding:
  - `normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded` (`buried-conditional`);
  - the Lemma 9.4 carriers `OsinLemma94PolygonRealizationInput`, `OsinLemma94CaseTwoInput`, `CornerInsertionInput`,
    `PendantPathRemovalInput`, `SeparatingPathRemovalInput`, `ChainRespellInput`, `OsinLemma94CuttingChainsInput`,
    `OsinLemma94CellArcsInput`, `OsinLemma94BoundaryArcsInput`, `OsinLemma94PolygonPartitionInput` and
    `QuasiGeodesicRespellInput` (`carrier-data`);
  - the producers `chainRespellInput_of_pieces`, `separatingPathRemovalInput_of_pendant` and
    `osinLemma94PolygonRealizationInput_of_pieces` (`open-predicate`).
- **Residual blind spot.** `separatingPathRemovalInput_of_pendant` builds its `Surgery.GFaceMerge` as the witness of an
  `obtain` over an existential (`OsinLemma94SeparatingRemoval.lean:89`). OsinLemma94DartMinimal obtains merges the
  same way (lines 81 and 126). The index still does not see them, so `facePerm_keep_of_ne` and `sigma_keep_eq_self`
  stay registered as "not a conditional".
  - systolic-counts took the fix and held it until merge 19 landed. It was told at 6457b79e5, and the next merge
    re-registers the baseline against it.

## register.py since d0aba6104

- **Clause revisions** (in place; each line keeps its key):
  - the count piece and the side budget: K after eps (9f8779c4e), and the patch ruled;
  - the residual assembly `osinLemma94Section_of_residuals`, which takes only the count and Case 1;
  - Case 1 has a producer (5be5cb6fc), and Case 2 is closed (e0e94015d);
  - the realization is closed over the partition (746028b24, 4002b9371);
  - the respelling, cutting-chain and arc pieces have producers;
  - the surgery modules are root-imported (65d0a4497, e0dcf8b99);
  - the hKO false red and the hKO leads, resolved by 736f7ea44;
  - the GFaceMerge blind spot, restated for the `obtain` witnesses.
- **New rules:**
  - premise `hhard`, written inline as the hard direction of the limit-set spelling, on
    `manuscriptSentence_hullGeneratingSetLimitSet` and `manuscriptSaturationLimitSet_of_leastAreaLeaves` (merge 18's
    two unclassified findings);
  - the cutting-chain pieces and their list and face-walk lemmas;
  - closed Case 2, with `osinLemma94CaseTwo_false`;
  - `osinLemma94Section_of_residuals`;
  - Hull's Lemma 3.5 at its printed generality, whose premises are the printed hypotheses (baseline-debt, b5f91627e).

## Merge tool changes (09-13)

- **Root-reachability.** A row stays `formalized` or `definition` only when every declaration it names lives in a
  module of the `GroupApproximation` import closure, per COMMON_RULES. A declaration that origin does not define, or
  that is compiled outside the closure, goes to the note, and the row is graded `partial` until the module is wired.
- **Resolve order.** A row resolves by a sentence key quoted in its note, then by the only candidate, then by text
  score with a margin, then by the unique sentence that starts at its line. Otherwise it is skipped as ambiguous.
- **DROP overrides.** `overrides.tsv` accepts `lane<TAB>given key<TAB>DROP<TAB>declarations<TAB>reason`. A row left
  with no declarations is skipped.
- **Revisions.** When a premise quoted in a registered line gets closed, register.py rewrites the justification, or
  the one stale clause wherever it occurs. The line ends with `[revised by the census merge at <sha>: <reasons>]`.
- **Landing.** The script checks the MSI master with `ssh -O check`, runs the passes detached, and lands the map, the
  census, both baselines and `notes/nm-swarm/WORKLIST.md` with `NM_BASE` set to the export sha.

## Overrides in force

- **Re-keys.** In both rows the note quotes the sentence, and the text match lost only on margin:
  - jacobson `LINE:1147` goes to `b6d1590be7ab`, the GHW / Kazhdan-subgroup sentence;
  - sec3-sentences `LINE:837` goes to `bd35898b630c` ("Since r=vwr+fr ...").
- **Retirements** (lead ruling of 2026-09-13 on debt-conditional groups B and C). All 19 lines were removed at
  94bb0a9f8.
  - sec5-sentences `LINE:1636`, `1644`, `1662`, `1665` and `1698` drop their historical quasi-geodesic and unbounded
    Lemma 4.4 carriers.
  - hull-respell `LINE:1636`/`1644` drop the three `_of_quasiGeodesicLeaves` declarations, and `LINE:1675` drops
    `osin24HullStep_of_boundedLeaves`.
  - These are the historical forms systolic-counts' flip report (20d0ec06d) leaves to census. They are decided, and
    systolic-counts was told at merge 19. At 6457b79e5 the retired forms appear only in map notes, never in a
    declaration column.

## Rows skipped

- **hull-respell `LINE:1636` and `LINE:1644`.** The DROP overrides removed every declaration, so both rows are
  skipped.
- **baseline-debt `LINE:1682`** (Hull Corollary 7.4 through Lemma 3.5). Skipped at merge 19 as ambiguous. The text
  scores were `dab2f2bfe084` 0.37, `02b6bf87400f` 0.25 and `26237422bf4c` 0.17, short of the margin, and no sentence key
  in its note resolved it. The note cites Corollary 7.4, and `dab2f2bfe084` is the only census sentence that does
  ("... by Hull's theorem~\cite[Corollary~7.4]{Hull} ..."). The other two are "Put $S=tJt^{-1}$." and "Since $J$ is
  simple and nonabelian ...". census re-keys the row to `dab2f2bfe084` in `overrides.tsv`, effective at the next
  merge.

## Carrier reachability

The merge checks every named declaration against the `GroupApproximation` import closure (6465 modules at 36ff632cd).

- At 6457b79e5 no map row carries a root-reachability note.
- At d0aba6104 two did: `8aead549f1fe` and `4895f03fdf5f`, over `OsinLemma94ChainRespell` and other carriers that
  were then compiled outside the closure.
- Both rows still name three declarations that origin no longer defines, all retired at b6bda9923:
  - `OsinLemma94PlanarRunInputReduced`;
  - `osinLemma94PlanarRunInput_of_reduced`;
  - `osinLemma94Section_of_planarRunInputReduced`.
  - By the lead's routing, they leave with sec5-sentences' next row update at `LINE:1636`.

## Open rows at 6457b79e5 (15 partial, by owner)

The keys are sentence keys. `notes/nm-swarm/WORKLIST.md` has the full sentences and declarations.

- **nm-endpoints (8):**
  - `a16637da7249` (tex 66, abstract);
  - `0f22bdbc4184` and `dce7a9ff4e83` (tex 285 and 291, thm:torsion-free);
  - `8aead549f1fe` and `4895f03fdf5f` (tex 1637, thm:hull);
  - `2f55113239ce` (tex 1651, lem:saturation);
  - `7b1fa3182135` and `8b1ec28a0e73` (tex 1719, cor:regular-nonmf-algebra).
- **cite-hull (4):**
  - `a9dd4b90e479` (tex 1629, Hull's generating set);
  - `bcc99703f838` (tex 1644, thm:hull);
  - `2d1cd22e5f49` and `2f997e5af4e6` (tex 1659, lem:saturation).
- **cite-hull, kh-ejz and nm-endpoints (2):** `8097c371f35d` and `dab2f2bfe084` (tex 1675, lem:saturation, Fournier-Facio's
  group).
- **sec5-sentences (1):** `721da4c14d11` (tex 1697).
- **Closed since d0aba6104:** `3009704fef89` (ghw-assembly, tex 1155) and `92115dd7edef` (sec5-sentences, tex 1728).

## hull-bridge name flips

hull-bridge maps 27 declarations over the least-area leaves to 21 `_of_greendlinger` forms. The old lines go stale at
the first merge after no row names an old declaration.

The counts at 6457b79e5 below are by suffix, not by hull-bridge's list.

- **Baseline.**
  - Lines naming an `_of_leastAreaLeaves` declaration: 43 (21 `buried-conditional`, 21 `open-predicate`, 1
    `inlined-statement`).
  - Lines naming an `_of_greendlinger` declaration: 114 (57 `buried-conditional`, 57 `open-predicate`).
- **Map and row files.**
  - 13 map rows name an `_of_leastAreaLeaves` declaration.
  - Besides hull-bridge's own rows, the row files name 17 distinct ones (sec5-sentences), 3 (cite-hull) and 1
    (hull-respell).

## Row files

- 37 row files are on origin.
- Row commits since 8bff272fa, all in the base of merge 0913-141044 (36ff632cd):
  - 92c643520 (hull-unbound): the cutting chains and respelling pieces;
  - 711c053f1 (baseline-debt): the closed Hull Lemma 3.5;
  - d82395558 (hull-unbound): the assembly over four residuals;
  - a719c860b (baseline-debt): the DGO 2.35 row moved to tex line 1728;
  - c62fbb481 (sec5-sentences): the closed Case 2;
  - 1b6c528fa (hull-unbound): the closed realization and the two-residual assembly;
  - 348fc1af7 (cite-ejz): the EJZ sentence row re-graded.
- No commit touching the rows, the verifier scripts or the root has landed since 6457b79e5 (checked at d4062cdf1).

## Next

- Re-merge whenever a lane lands rows, and at least every ~2 h.
- systolic-counts: the `obtain` witnesses of `Surgery.GFaceMerge`. The next merge re-registers against the fix.
- Lemma 9.4: the side-budget patch (hull-count94, sec5-sentences) and the Case 1 composition, patch 10(f)
  (ghw-charp2, theoremc-retire).
- sec5-sentences' three stale declaration names at `LINE:1636` ride along with its next row update.
