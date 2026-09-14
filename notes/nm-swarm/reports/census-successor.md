# census-successor: census merge after the census lane stopped

Lane ms-cite-2 acts as census-merge successor (main's item, 2026-09-13 ~18:25 CDT).

- The census lane has been stopped since its coordinator went down at 17:56.
- The last census landing before this successor was 6457b79e5 (14:17, base 36ff632cd). It carried the manuscript hash
  from before 45483f699, with 498 sentences.
- Merge 0913-171131 (base 4af014f74) did not land: REGISTER exited 3 on two unclassified findings.

## Procedure (gates unchanged)

Every pass runs on MSI through the census tools, detached on the node and polled for `SENTINEL=done`:
1. `merge_rows.py` unions the row files per sentence, applies compiled-evidence and root-reachability downgrades and
   restorations, and applies `overrides.tsv`;
2. the census tsv and md are regenerated;
3. `register.py` keeps `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` in step;
4. worklist, `--check`, `--verify-decls`, `--verify-unconditional`.

The script lands the map, the register, the census tsv and md and `notes/nm-swarm/WORKLIST.md` as lane `census`, with
`NM_BASE` set to the export sha. It lands only when MERGE, WRITE, REGISTER, WORKLIST, VERIFY_DECLS and VERIFY_UNCOND
are all 0, and only when the shared tree's copies equal origin at the export sha. `--check --require-complete` stays
red on partial and unassigned rows, which is the true state.

## Successor changes

The successor tools live in `$NM/census/`, in this session's scratchpad `nm/`. Origin's 09-12 originals are kept in
`$NM/census/orig-0912/`.
- The laptop reboot of 09-14 ~08:2x wiped `/private/tmp`, including the first copies in `ct/census/` and the census
  lane's scratchpad.
- `merge_rows.py`, `register.py`, `worklist.py`, `census_linemap.py`, `overrides.tsv` and `run.sh` were restored from
  MSI `cc-in` of merge 0914-015152, with the same md5 as before the wipe.
- `census_merge.sh` and `partial_triage.sh` were recreated. The `run.sh` that the recreated script writes matches the
  restored `run.sh` byte for byte.

- **LINE keys of the new lanes.** `census_linemap.py` carries `LINE:<n>` from the tex at a8cc132c8 (before
  45483f699). The lanes launched by session nonsofic-existence-49 (`ct-*`, `ms-*`, `w1-*`) number LINE keys at the
  current tex (68481e4d7 and later).
  - Merge 0913-171131 carried ct-rank-budget `LINE:1700` to 2185 and skipped nine ct rows as ambiguous.
  - `merge_rows.py` now reads LINE keys of lanes matching `CURRENT_TEX_LANES` (default `^(ct|ms|w1)-`) without the
    line map. Other lanes keep the a8cc132c8 map.
  - The trial after the fix resolved every ct row.
- **Register rules.**
  - Two specific rules for the open assembly of `cor:dynamic-rank-budget`: `PrintedDynamicRankBudget` and
    `printedDynamicRankBudget_of_pieces`, which name the eight residual piece Props and their owners.
  - A guarded rule for the open named residuals of the chain-core tail (`ChainCore.*`, `ClopenCrossedProduct.*`). It
    registers a carrier-data, open-predicate or buried-conditional finding only when every row citing it is graded
    partial or open in the census the merge just wrote. The line names the premises and owners. A finding cited by a
    formalized or definition row stays UNCLASSIFIED, so the gate stays red.
- **Overrides**, effective at the next merge.
  - chain-itinerary is down, and ms-compress-1 re-graded three of its rows at bd7b20b28, carrying each old residual.
  - DROP overrides remove chain-itinerary's rows on `fe2bd83087c0`, `ed348643e2ad` and `807793f12a5e`, so
    ms-compress-1's rows grade those sentences instead of a union with the stale partial rows.
- **KEEPLATEST overrides** (new form, merge 2).
  - `lane<TAB>given key<TAB>KEEPLATEST<TAB>reason` keeps only that lane's last row at that given key. It is for rows
    their writer declared superseded without writing SUPERSEDES in the note.
  - The union rule is otherwise unchanged: several rows of one lane at one key are united, and any partial row makes
    the sentence partial.
  - A scan of every row file at 19:3x found three such keys, all in ct-bilateral-mf: `LINE:1541`, `LINE:253` and
    `LINE:1760`. ct-rank-budget regraded the latest rows at 2fb94570a on the lead's order, and the older 816a6b699 rows
    stay in the file.
- **DROP overrides from ms-core-4's findings** (main's order 23:12, effective at merge 5).
  - ct-bilateral-mf `LINE:1594`: `relativeElementary_killed_of_rootThree_killed`, carried by
    `printedBilateralThreeRootAddition_closed` (ChainCoreSweepClosed, f107803fc).
  - ct-bilateral-mf `LINE:1599`: `not_isOperatorMF_of_root_killed`, carried by `printedNotDirectlyFiniteGLNotMF_closed`.
  - sec5-sentences `LINE:1629`: all six declarations. The row is skipped, and `a9dd4b90e479` grades from the cite-hull
    and ms-torsionfree rows.
- **SUPERSEDE overrides** (new form, merge 5).
  - `lane<TAB>given key<TAB>SUPERSEDE<TAB>declarations<TAB>reason` replaces that lane's rows at the given key by one
    formalized row naming only the given declarations. Later rows of the lane at that key are skipped.
  - The named declarations still go through the defined, compiled and root-reachable checks and the verifier. So a
    superseded row grades formalized only once its closed endpoints are wired.
  - Entries come from ms-core-4's owner supersedes, where the owner lanes are not resumed:
    - ct-bilateral-mf `LINE:1598`, `LINE:1599` and `LINE:1600` name `printedBilateralThree_closed`,
      `printedBilateralThreeRootAddition_closed` and `printedNotDirectlyFiniteGLNotMF_closed`. `LINE:1541` keeps its
      KEEPLATEST, whose latest row already names `printedBilateralThree_closed`.
    - ms-core-5 `2b6b9904f2d6` names `coreMFRadicalKillGLStatement_holds`.
    - ms-core-3 `50c5dd41dff4`, `5c06eec5555b` and `1c114e2c4209` name `coreKernelElementaryStatement_holds` and
      `printedInvolutionLocalization_closed` (TransientCellsClosed).
- **`LINE:1743` re-key** (merge 5). ct-rank-budget's `LINE:1743` row goes to `1cddd9e4b7ba` ("The induced core is
  $C\cap Y$."), whose carrier `printedInducedCore_closed` it names.
  - At 75dab9892 ct-rank-budget keyed the other four sentences of tex 1743–1750 by their own rows: `7da9f1c6076f`,
    `8f8f0c7b59fa`, `d5dcf496d149`, `e7f732e9cb78`. Their per-sentence carriers are in
    DynamicRankBudgetInducedCoreSentences (6387112a8).
  - `merge_rows.py` also accepts a re-key to several space-separated sentence keys, for a row whose note quotes each of
    them. No entry uses it now.
- **Fetch retry.** `census_merge.sh` retries its opening `git fetch` up to six times.
- **Partial triage** (`$NM/census/partial_triage.sh`, from merge 5 on).
  - A partial sentence is wiring-only when the merge DOWNGRADED it from formalized or definition for root reachability,
    the verifier has no conditional finding for it, and no named declaration is undefined or uncompiled.
  - Every other partial sentence is listed with its residual and owner lanes.
  - On merge 4's outputs this gives 2 wiring-only and 73 listed. The wiring-only counts given for merges 1 to 4 below
    counted every row with a root-reachability note, so they are upper bounds.
- **DROP overrides from ms-core-1's sweep before tex 1541** (19 lines, `$NM/census/drop-lines-ms-core-1.tsv`,
  effective at merge 6).
  - Checked against the row files at origin 3ea243dda.
    - 18 lines retire a lane's single partial row at a sentence key, and every declaration they list is in that row.
    - Each of those keys keeps a formalized row from another lane: ms-core-1 (04240efed), ms-core-2, ct-return-tower,
      ms-traces-3, ms-inverses-3 or ms-units.
  - The lanes are chain-reflection (10 keys), chain-itinerary (2), chain-subshift (2), hull-euler (2), ms-compress-1
    (`b180421b55ab`) and ms-core-4 (`f0c16e5c8519`).
  - leavitt-units `f6962254d259` drops only the helper `elementary_le_commutator_of_trivial` from a formalized row, which
    keeps its other two declarations. This retires the register's tex-1321 inlined-statement finding.

## Merges

| merge | base | result | formalized | definition | structural | partial | unassigned | total |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0913-183126 (trial) | e336f6734 | no land: REGISTER=3, 17 unclassified (chain-core tail residuals) | 299 | 51 | 51 | 193 | 86 | 717 |
| 0913-185744 | da89370bf | **LANDED b75e5bbcd**, verified on origin | 299 | 53 | 51 | 197 | 80 | 717 |
| 0913-195235 | fc77250a3 | **LANDED f78d19014** (20:02), verified on origin | 325 | 63 | 54 | 226 | 12 | 717 |
| 0913-202315 | 484a4b651 | **LANDED 3f3f4c5c3**, verified on origin | 381 | 69 | 54 | 164 | 12 | 717 |
| 0913-212820 | 16d890864 | **LANDED 0e622f840**, verified on origin | 473 | 72 | 55 | 75 | 5 | 717 |
| 0913-233549 | 8d833d5fd | **LANDED a4f8d4b82**, verified on origin | 482 | 72 | 55 | 70 | 1 | 717 |
| 0914-015152 | 4c3d9dd02 | **LANDED 5d8014be4** (02:00), verified on origin | 495 | 73 | 55 | 57 | 0 | 717 |

Merge 0913-185744:
- **Register:** 3 stale lines removed, 201 revised, 30 new registered, 0 unclassified.
- **Verifiers:** `--verify-decls` 0 missing; `--verify-unconditional` 468 accepted, 0 new.
- **Downgrades from origin's map:** 49 formalized, 5 definition and 4 structural rows went to partial. Every one
  carries a merge note.
  - Of the 197 partial rows, 169 are partial only because a carrier module is compiled outside the
    `GroupApproximation` import closure.
  - Most of those come from ms-* re-grades that name new, not-yet-wired carriers. The next merge after wiring restores
    them.
- **Unassigned (80):** 77 in sec:chain-core, 3 in the Introduction.

Merge 0913-195235 launched at 19:52 and landed at 20:02, just before the ~20:03 API outage.
- **Base:** fc77250a3. It includes lead-wire ef5f85c15 (15 modules) and the rows of ms-compress-1 (bd7b20b28) and
  ct-rank-budget (2fb94570a, 07a74132c).
- **Register:** 17 stale lines removed, 0 revised, 0 new, 0 unclassified. `--verify-unconditional`: 410 accepted,
  0 new.
- **Partial (226):** 217 are partial only because a carrier module is outside the root closure. Partial rose from
  197 mainly because formerly unassigned rows were assigned as partial.
- **Overrides applied:** the three chain-itinerary DROPs and the three ct-bilateral-mf KEEPLATESTs. At `LINE:1760` the
  union now holds one row each from ct-bilateral-mf and ct-rank-budget. ct-rank-budget's regraded rows stay partial
  until `ChainCoreClosures` (b09de1dcf) and `CoreModelsLEFClosed` are wired.
- **Skipped as BAD-KEY:**
  - lix-descent's row keyed `LINE:none` (`metadata/nm-census-rows/lix-descent.tsv`);
  - two sk-ms-core-3 rows keyed `LINE:131@2050a8eed` and `LINE:134@2050a8eed`. That file sits only in the census
    lane's scratchpad rows directory and looks like a simple Kazhdan note row filed there by mistake.
- **Next:** lead-wire 6425614c8 (36 modules, 20:02) landed after this export, so merge 0913-202315 (base 484a4b651)
  was launched over it after the resume.

Merge 0913-202315 launched at 20:23 and landed as 3f3f4c5c3.
- **Base:** 484a4b651, which includes lead-wire 6425614c8 (36 modules).
- **Register:** unchanged (0 stale, 0 revised, 0 new, 0 unclassified). `--verify-unconditional`: 410 accepted, 0 new.
- **Restored by the wiring:** 56 rows went from partial to formalized and 6 from partial to definition. No row went
  down.
- **Partial (164):** 117 are partial only because a carrier module is outside the root closure.
- **Next:** ct-rank-budget's `LINE:1743` row (8ec0cc7fb) landed after this export, so the next merge takes it. Its
  carrier is `printedInducedCore_closed`, in DynamicRankBudgetInducedCoreClosed (2829a1eb9).

Merge 0913-212820 launched at 21:28 and landed as 0e622f840.
- **Base:** 16d890864, which includes lead-wire a1f1820bd (wave 19, 36 modules).
- **First launch:** at ~21:26 it exited 1 at its opening `git fetch`, before exporting anything. The cause was a
  ref-lock race with another fetch. The retry ran clean.
- **Register:** unchanged (0 stale, 0 revised, 0 new, 0 unclassified). `--verify-unconditional`: 411 accepted, 0 new.
- **Restored by the wiring:** 89 rows went from partial to formalized. No row went down.
- **Partial (75):** 3 are partial only because a carrier module is outside the root closure.
- **Skipped as AMBIGUOUS:** ct-rank-budget's `LINE:1743` row (8ec0cc7fb).
  - Its note quotes tex 1743–1750, starting with the sentences `1cddd9e4b7ba` ("The induced core is $C\cap Y$."),
    `7da9f1c6076f` and `8f8f0c7b59fa`.
  - The text match tied at 1.20 between the first two.
- **Skipped as STALE-KEY:** sk-ms-core-3's three rows, which now carry sentence keys from another census.

Merge 0913-233549 launched at 23:35 and landed as a4f8d4b82.
- **Base:** 8d833d5fd, which includes lead-wire 7d71bbbd1 (36 modules).
- **Overrides applied for the first time:** ms-core-4's three DROPs, the seven SUPERSEDE entries and the `LINE:1743`
  re-key. All ten target sentences now grade formalized: `7f55f9a11e5a`, `0f83142a750a`, `2016c672dd6a`,
  `d812630a48ab`, `2b6b9904f2d6`, `50c5dd41dff4`, `5c06eec5555b`, `1c114e2c4209`, `a9dd4b90e479` and `1cddd9e4b7ba`.
- **Register:** 2 stale lines removed, 0 revised, 0 new, 0 unclassified. `--verify-unconditional`: 408 accepted, 0 new.
- **Grades:** 9 rows went from partial to formalized. No row went down.
- **Partial (70):** by `partial_triage.sh`, 9 are wiring-only and 61 have residuals.
  - ct-rank-budget's four new rows at 75dab9892 (`7da9f1c6076f`, `8f8f0c7b59fa`, `d5dcf496d149`, `e7f732e9cb78`) are
    partial. Their carrier module, DynamicRankBudgetInducedCoreSentences, is queued for wiring.
- **Next:** lead-wire daa821b00 (32 modules, 23:41) landed after this export, so merge 6 was launched right after.

Merge 6 took six attempts: the first five failed on the network, and the sixth landed (below).
- At ~23:5x its opening fetch failed six times with `Could not resolve host: github.com`.
- At 00:19 the script stopped at its own check, because the MSI master was down.
- At 00:37 (tag 0914-003758, base a0c769367) the master dropped during the sync, with "Broken pipe" and an ssh timeout.
  The script exited 4 before launching anything on the node.
- Nothing was exported or installed, and the census on origin stays at a4f8d4b82. At 01:00 github.com again did not
  resolve and the master socket was gone.
- Merge 6 runs once github.com resolves and the MSI master is back. It applies ms-core-1's DROPs over daa821b00.
- **audit-nm-1's rows for tex 1–1337** come from its fidelity audit of 0e622f840 (ledger a0c769367). They are written as
  `metadata/nm-census-rows/audit-nm-1.tsv` and land on audit-nm-1's behalf as soon as github.com resolves, so merge 6
  takes them.
  - Four grade a sentence partial for a generality or route gap:
    - `d4c878a7ac22`: no `Countable W`;
    - `2a97fb901bad`: a different route;
    - `80279f06992b`: the `EL_n` clause needs a prime characteristic;
    - `2ff745dd7064`: 4 ≤ n and no nontriviality.
  - Spot checks against the Lean source agree with the ledger for `d4c878a7ac22` and `80279f06992b`. For
    `2ff745dd7064`, the prime-characteristic form of the statement also quantifies 4 ≤ n.
  - Three add a closed carrier for an uncovered clause: `c890294ad9b0`, `2d6ab84875e0` and `8d0b87a46a51`.
- **audit-nm-4's row for tex 1338–2507** comes from its fidelity audit of 0e622f840: 232 rows, 231 PASS, 0 false green.
  It is written as `metadata/nm-census-rows/audit-nm-4.tsv`.
  - It grades `f5264e48f943` (tex 1489) partial. `exists_wandering_clopen_cover` takes `IsClopen K`
    (Dynamics/TransientSupport.lean:212), where the manuscript prints "A compact subset $C\subset U$".
  - The owner ms-inverses-3 is told and may add a compact-to-clopen lemma instead.
  - audit-nm-4's other notes are for owner lanes, not overrides:
    - rows `1baaaaa0fb29` and `69ef136d809a` could name `defectIdeal_eq_transientIdeal_chainRecurrentSet`;
    - `8cde0b44b52f` could name `manuscriptSentence_reassociation`;
    - the map note of `c650b0a20b89` quotes the next sentence.
- **Landing chain.** github.com failed to resolve again at 01:19. Neither row file reached origin, and merge 6's fourth
  attempt exited 1 at its fetch.
  - `ct/census/chain-s6.sh` waits until github and the MSI master are both up on two checks 60 s apart.
  - It then lands both row files, confirms each on origin, and runs merge 6, retrying on network exits.
  - The chain landed audit-nm-1's rows at 0be73ce26 (01:44) and audit-nm-4's row at 4c3d9dd02 (01:45).
  - Its first merge attempt (tag 0914-014629) failed in the sync, when the master dropped with "Permission denied".
    The second landed.

Merge 0914-015152 launched at 01:51 and landed as 5d8014be4 at 02:00.
- **Base:** 4c3d9dd02. It includes lead-wire daa821b00 (32 modules), ms-core-1's DROPs, audit-nm-1's rows and
  audit-nm-4's row.
- **Master drops:** the poll found the MSI master down on 7 checks. The detached passes finished on the node.
- **Register:** 1 stale line removed, 0 revised, 0 new, 0 unclassified. `--verify-unconditional`: 407 accepted, 0 new.
- **Grades:**
  - 18 rows went from partial to formalized, and 1 from partial to definition.
  - 5 went from formalized to partial, all by audit rows: `d4c878a7ac22`, `2a97fb901bad`, `80279f06992b` and
    `2ff745dd7064` (audit-nm-1), and `f5264e48f943` (audit-nm-4).
- **ms-core-1's DROPs:** 15 of the 19 target sentences grade formalized. The other 4 (`30a44485e5e8`, `715cbd0f3410`,
  `f2baa4a46f78`, `b180421b55ab`) are wiring-only, because a carrier module is outside the root closure.
- **Unassigned:** none. ct-rank-budget's `d59fc0887768` row (a407d436d) grades partial until ChainCoreOpeningSentence is
  wired.
- **Partial (57):** by `partial_triage.sh`, 9 are wiring-only and 48 are listed in the triage section below.

## Re-merge triggers

- After each ROOT GREEN wiring wave by ms-core-5, the root-wire successor (`notes/nm-swarm/reports/root-wire-successor.md`).
  - A wave lands as a "Wire N landed non-MF campaign module(s) into the root" commit on `GroupApproximation.lean`.
  - Wave 16 was c0c1a8e3d (16:32). The next wave, 15 ct/ms modules, landed as ef5f85c15 at 19:27 and triggered merge 2.
- Whenever lanes land rows, and at least every ~2 h.

## Partial rows that are not wiring-only (merge 0914-015152, 5d8014be4)

From `partial_triage.sh`: 57 partial, 9 wiring-only, 48 listed. The residual is the open premises named by the key's
conditional findings, or the row's own note when there is no finding. Owner lanes are the lanes whose rows the map row
unites. This section is replaced at each merge.

| key | tex | residual | owner lanes |
| --- | --- | --- | --- |
| `a16637da7249` | 66 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement  | ct-rank-two-limit fff-periodic nm-endpoints |
| `d4c878a7ac22` | 263 | graded partial by its row, no conditional finding: audit-nm-1: PrintedAmenableNonquasidiagonalTrace binds ∃ W … ¬IsOperatorMF W without Countable W; MF is printed only for countable groups (tex 87 | audit-nm-1 |
| `2a97fb901bad` | 270 | graded partial by its row, no conditional finding: audit-nm-1: printed route "direct limit of RF groups ⇒ MF [Korchagin Cor 10, Prop 13]"; the carrier goes locally RF ⇒ LEF ⇒ MF; no MF direct-lim | audit-nm-1 |
| `80279f06992b` | 292 | graded partial by its row, no conditional finding: audit-nm-1: the EL_n clause needs (p:R)=0 with 0<p, but the examples above include EL₄(𝒞) with 𝒞=ℤ⟨s,t⟩/(tᵢsⱼ−δᵢⱼ) and every  | audit-nm-1 ms-intro-3 |
| `abb56744db26` | 292 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedTorsionFreeTheorem  | ms-intro-3 sec5-sentences |
| `0f22bdbc4184` | 297 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedTorsionFreeTheorem FournierFacioParagraph PrintedTorsionFreeTheoremOsin  | ct-rank-two-limit fff-periodic hull-bridge nm-endpoints sec5-sentences theoremc-retire |
| `dce7a9ff4e83` | 303 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement FournierFacioParagraph  | ct-rank-two-limit fff-periodic nm-endpoints sec5-sentences |
| `2ff745dd7064` | 1072 | graded partial by its row, no conditional finding: audit-nm-1: PrintedElementaryGroupNotMF quantifies 4≤n and displays no nontriviality; printed at the corollary's n≥2 with "countable and nontrivia | audit-nm-1 audit-sec3 |
| `f5264e48f943` | 1489 | graded partial by its row, no conditional finding: audit-nm-4 GENERALITY-GAP (fidelity audit of tex 1338-2507 at merge 0e622f840: 232 rows, 231 PASS, 0 FALSE-GREEN): exists_wandering_clopen_cover needs | audit-nm-4 ms-inverses-3 |
| `ff376e50f433` | 1489 | graded partial by its row, no conditional finding: ms-inverses-3: tex 1491-1492, "Erasing loops shortens any path between related points to at most m-1 steps"; the conclusion is proved by stabilization | ms-inverses-3 |
| `1d0f9a56866c` | 1502 | graded partial by its row, no conditional finding: ms-inverses-3: tex 1497-1499, "Choose a finite clopen partition of C separating distinct points in each class ... compactness gives such a partition"; | ms-inverses-3 |
| `46f3810145ee` | 1502 | graded partial by its row, no conditional finding: ms-inverses-3: tex 1500-1502, "The representative set is clopen, because presence of a related point in an earlier atom is a finite clopen test"; the  | ms-inverses-3 |
| `5079b22a3633` | 1502 | graded partial by its row, no conditional finding: ms-inverses-3: tex 1502-1503, "Refine it according to the occupied atoms, the shift exponents to each level, and all original coefficient values"; exi | ms-inverses-3 |
| `fd026a61f84f` | 1502 | graded partial by its row, no conditional finding: ms-inverses-3: tex 1499-1500, "Order its atoms and select the point in the first occupied atom as the class representative"; the representative is the | ms-inverses-3 |
| `30e2f83b735e` | 1550 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1552-1553, "Wandering gives f_ab f_ce = delta_bc f_ae", for every cell of every ring. LANDED 923231b3c/5d90422ea; closed, pendi | ct-bilateral-cell |
| `331807e9e898` | 1550 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1550-1552 (proof of prop:bilateral-three), "Take a clopen P with T(P) in P and nonempty D=P minus T(P). Put p=1_P, d=1_D, and f | ct-bilateral-cell |
| `7753d17ede98` | 1550 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1554-1555, "The unital subalgebra S in pR_Xp generated by s=up, t=pu^-1 and kp satisfies ts=p, st=p-d": S = cellRing (the subri | ct-bilateral-cell |
| `8a69e48d6382` | 1550 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1553, "Negative levels lie outside P": p f_ab = 0 for a<0 and f_ab p = 0 for b<0. LANDED 923231b3c/5d90422ea; closed, pending r | ct-bilateral-cell |
| `9a398d134788` | 1550 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1557-1558, "Embed it in GL_3(R_X) by adjoining identity on 1-p": g -> diag(1-p) + g, injective, image the root subgroup over S. | ct-bilateral-cell |
| `ca8edac58ba3` | 1550 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1556-1557, "It is finitely generated, so L=EL_3(S) has property (T)": S finitely generated (closed); (T) of the embedded copy v | ct-bilateral-cell ct-bilateral-mf |
| `732be542bd63` | 1560 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1560-1564, "Let r cycle the three negative levels -1 -> -2 -> -3 -> -1: r = ..., W = diag(u,u,u) diag(1,1,r)": r, its inverse c | ct-bilateral-cell |
| `0fa967251251` | 1566 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1568-1569, "On its third coordinate W fixes the negative levels -1 and -2 individually", in the form used: (ur) f_{-1,-2} = f_{ | ct-bilateral-cell |
| `4a0223a24da4` | 1566 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1571-1575, "Put c=e13(f_{-1,-2}), l=e21(p), y=e32(f_{-1,0}), z=1+E33 f_{-1,-2}, B=<L,W,c,y>". LANDED 5d90422ea; pending root wi | ct-bilateral-cell |
| `4a343ef108b1` | 1566 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1566-1568, "Thus W conjugates L into L, sending a root coefficient a in S to uau^-1=sat". LANDED 5d90422ea/41d8c3b03; pending r | ct-bilateral-cell |
| `f60fa6d3b787` | 1566 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1566, "The correction r acts outside P and centralizes L": r a = a = a r on the corner pRp, so W acts on corner roots by u. LAN | ct-bilateral-cell |
| `4f649a2dcbfa` | 1577 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1577-1582, "Then c in C_B(L) and WcW^-1=e13(f_{0,-2}), delta=[WcW^-1,l]=e23(-f_{0,-2}), [y,delta]=z^-1", with Mathlib's commuta | ct-bilateral-cell |
| `10fe7a237145` | 1583 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1589-1594, "The identities [z,e31(f_{-2,0})]=e31(f_{-1,0}), [e23(f_{0,-1}),e31(f_{-1,0})]=e21(d) then kill the defect root": bo | ct-bilateral-cell ct-bilateral-mf |
| `15fba9954989` | 1583 | graded partial by its row, no conditional finding: ct-bilateral-cell: tex 1583-1585, "It commutes with L, since both its supports lie outside P; with W, since its two levels are fixed; and with c,y, by | ct-bilateral-cell |
| `3550126258fb` | 1583 | graded partial by its row, no conditional finding: ct-bilateral-mf: tex 1587-1588, "Theorem thm:compression-criterion kills z under every MF homomorphism from B, hence from GL_3(R_X)." via manuscriptOn | ct-bilateral-mf |
| `cd7908a482b5` | 1583 | graded partial by its row, no conditional finding: ct-bilateral-mf: tex 1583, "Hence z in D_B(L)." proved inside killed_of_finite_central_defect from [y,[WcW^-1,l]] = z^-1 (printedDefect_generator_mem) | ct-bilateral-mf |
| `e94a87793eb1` | 1583 | graded partial by its row, no conditional finding: ct-bilateral-mf: tex 1583-1587, "It commutes with L ... So <z> is a nontrivial finite central subgroup of B, of order char(k)." central and finite in  | ct-bilateral-mf ms-inverses-4 |
| `07ab0fbe6cfc` | 1673 | graded partial by its row, no conditional finding: ct-involution: tex 1678-1680, the printed proof refines the matrix-block construction of lem:transient-matrices by K and C; Lean uses the piecewise pl | ct-involution |
| `3468c60b2946` | 1673 | graded partial by its row, no conditional finding: ct-involution: tex 1681-1682, the 2m distinct return times of each point are card_returns_ge; generated classes are not formed on this route (see 07ab | ct-involution |
| `6baf73489057` | 1673 | graded partial by its row, no conditional finding: ct-involution: tex 1685-1686, the matching is constant on the clopen cells A j h, a finite clopen partition of K, but not the representative cells of  | ct-involution |
| `60708f733247` | 1731 | graded partial by its row, no conditional finding: ct-bilateral-mf: tex 1732-1733, "Thus R_X is a unital corner of M_{2r-1}(P_C), via x -> (b_i x a_j)_{ij}": the injective non-unital map into M_{2r-1}( | ct-bilateral-mf ct-return-tower |
| `9e22ceae062f` | 1739 | graded partial by its row, no conditional finding: ct-bilateral-mf: tex 1739, "Unitization embeds GL_{nr}(P_C) into GL_n(R_X)." GL_{n r}(A) -> GL_n(R) and GL_r(A) -> R^x (n = 1) injective, over the ide | ct-bilateral-mf ct-return-tower |
| `f1769ba5e51c` | 1739 | graded partial by its row, no conditional finding: ct-bilateral-mf: tex 1740-1741, "For n>=2, block elementary flattening puts the image of EL_{nr}(P_C) inside EL_n(R_X)." injective EL_{n r}(A) -> EL_n | ct-bilateral-mf ct-return-tower |
| `4895f03fdf5f` | 2122 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement OsinLemma94PlanarRunInput OsinLemma94PolygonCountInput OsinLemma94CaseOneInput OsinLemma94UnboundSameCellStatement OsinLemma94PolygonSideBudgetInput ClassBudget K ClassCovers M L ∀ rho' : ℕ, rhom ≤ rho' → OsinLemma94DensePolygonsAntiparallel (symmetricLabelAlphabet D)… OsinLemma94ClassCountInput DartMinimal UnselectedGFace f RunsBackAcross chain UnselectedGFace first DegreeTwoJoints path GFacesApart CellArcsQuasiGeodesic BoundaryArcsQuasiGeodesic CuttingChainsQuasiGeodesic OsinLemma94PinchedQuadrilateralStatement LeastArea inv l) PrintedHullSmallCancellationCurrent PrintedHullSmallCancellationOsin PrintedHullSmallCancellationLimitSet OsinLemma94DensePolygonsAntiparallel D lambda c eps rho K OsinLemma94KindTransitionInput OsinLemma94LongTransitionInput  | audit-intro ct-rank-two-limit fff-periodic fff-quotient hull-bridge hull-count94 hull-unbound nm-endpoints sec5-sentences |
| `8aead549f1fe` | 2122 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement OsinLemma94PlanarRunInput OsinLemma94PolygonCountInput OsinLemma94CaseOneInput OsinLemma94UnboundSameCellStatement OsinLemma94PolygonSideBudgetInput ClassBudget K ClassCovers M L ∀ rho' : ℕ, rhom ≤ rho' → OsinLemma94DensePolygonsAntiparallel (symmetricLabelAlphabet D)… OsinLemma94ClassCountInput DartMinimal UnselectedGFace f RunsBackAcross chain UnselectedGFace first DegreeTwoJoints path GFacesApart CellArcsQuasiGeodesic BoundaryArcsQuasiGeodesic CuttingChainsQuasiGeodesic OsinLemma94PinchedQuadrilateralStatement LeastArea inv l) PrintedHullSmallCancellationCurrent PrintedHullSmallCancellationOsin PrintedHullSmallCancellationLimitSet OsinLemma94DensePolygonsAntiparallel D lambda c eps rho K  | ct-rank-two-limit fff-periodic fff-quotient hull-bridge hull-count94 hull-unbound nm-endpoints sec5-sentences |
| `bcc99703f838` | 2129 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedHullProofParagraph  | ct-rank-two-limit fff-periodic hull-bridge sec5-sentences |
| `2f55113239ce` | 2136 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedSaturationLimitSet IsAcylindricallyHyperbolicLimitSet G → GGT…  | ct-rank-two-limit fff-periodic hull-bridge nm-endpoints sec5-sentences |
| `2d1cd22e5f49` | 2144 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedSaturationPairAndHullAgain  | cite-hull ct-rank-two-limit fff-periodic hull-bridge sec5-sentences |
| `2f997e5af4e6` | 2144 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedSaturationApplyHull  | ct-rank-two-limit fff-periodic hull-bridge sec5-sentences |
| `8097c371f35d` | 2160 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement FournierFacioParagraph LiteratureInputs  | ct-rank-two-limit fff-periodic hl-lemma46 hull-bridge hull-respell kh-ejz kh-torsion ko-closed nm-endpoints sec5-sentences simple-group |
| `dab2f2bfe084` | 2160 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement HullOneStepStatement PrintedHullCorollary74 HullTowerStatementGeneral  | baseline-debt cite-hull ct-rank-two-limit fff-periodic hull-bridge ms-torsionfree nm-endpoints |
| `721da4c14d11` | 2182 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedTheoremApplySaturation  | ct-rank-two-limit fff-periodic hull-bridge sec5-sentences |
| `7b1fa3182135` | 2204 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedRegularNonMFAlgebra FournierFacioParagraph PrintedRegularNonMFAlgebraOsin  | ct-rank-two-limit fff-periodic hull-bridge nm-endpoints sec5-sentences |
| `8b1ec28a0e73` | 2204 | open premises: RelativeGreendlingerQuasiGeodesicLeastAreaStatement PrintedRegularNonMFAlgebra FournierFacioParagraph PrintedRegularNonMFAlgebraOsin  | ct-rank-two-limit fff-periodic hull-bridge nm-endpoints sec5-sentences |
