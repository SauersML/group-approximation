# MS-WORKLIST: EVERY line of both manuscripts, unconditionally (owner ms-map; v3 2026-09-19 10:45 CDT)

USER ORDER (09-19): every line of non_mf_groups_exist.tex and simple_kazhdan_sofic_group.tex, 100% unconditional.
Main read at 6a3f0c6cc (09-19 14:49Z) plus ms-map's census batch 691b03881 (NM).
The censuses (tsv/md) are the 09-18 00–02Z generation and are regenerated on MSI by the item-0 job (section E).
Claim a row or item by appending `CLAIMED <lane> <time>` under it; put progress lines under the item.

## L. LIVE COUNT: rows NOT yet unconditional (ms-map keeps this current)
- NM: 717 rows. 658 complete (528 formalized + 75 definition + 55 structural). 22 partial. 37 attribution/provenance (6 of them assert mathematics).
- SK: 228 rows (census 4384927d3): 216 complete (171 formalized + 26 definition + 19 structural), **0 open**, 12 attribution. Of those 12, 2 still assert mathematics (e5932a45f053 Grigorchuk–Medynets, S2; fc84c012b409(b), S3), 768ac9454e9b is cited background, and 9 are history.
- Build caveat: no endpoint module of either note has a green MSI build on current main. Slurm has been blocked since 09-18 20:55 (item C).

| # | census | rows (key @tex line) | what is owed | owner(s) |
|---|---|---|---|---|
| N1 | NM | 15 waist rows: a16637da7249@66, abb56744db26@294, 0f22bdbc4184@299, dce7a9ff4e83@305, 8aead549f1fe@2135, 4895f03fdf5f@2135, bcc99703f838@2142, 2f55113239ce@2149, 2d1cd22e5f49@2157, 2f997e5af4e6@2157, 8097c371f35d@2173, dab2f2bfe084@2173, 721da4c14d11@2195, 7b1fa3182135@2217, 8b1ec28a0e73@2217 | hG (relative Greendlinger) = residual (i) GL06e AllCellsShortEnclosedRefutedBelowSectionStatement + residual (ii) GL03DKept gl03dKept_KeptSubwalkCoreStatement | (i) **nm-gl06e**, (ii) **nm-gl03d**; regrade on closure: ms-nm-partial-b (11 rows), ms-nm-partial-a (a166, abb5, 0f22, dce7) |
| N1a | NM | the same 8aead549f1fe, 4895f03fdf5f | 29 Osin 9.4 register lines (alternative route); they collapse once hG has a closed producer (plan 66d8a812c) | **nm-osin94** |
| N2 | NM | 7 route rows: 1d0f9a56866c, fd026a61f84f, 46f3810145ee, 5079b22a3633 @1510; 07ab0fbe6cfc, 3468c60b2946, 6baf73489057 @1685 | proved at source (Full/NMRegradeA over NM19, f7e7fbf92). Unprobed and not root-wired, so HELD partial (691b03881) | probe: ms-nm-partial-a; wire + flip: ms-map |
| N3 | NM | literature claims in attribution rows: 14ee41b7f3cc@312 (BK97 NF iff nuclear + inner QD), de554b7cd342@338 (Kun, Kun–Thom), 9e2046c330c8@338 (Bachner–Dogon–Lubotzky), a494a9e94d28@338 (Eckhardt) | not used by any proof. They need Lean statements and proofs, or a census-owner ruling that they are background. | UNOWNED: needs a lane (ms-map triage) |
| N3a | NM | afe1782dc7bc@1273 (AGP facts) | `manuscriptAGPInputs` is a proved theorem; regrade attribution → formalized (NM batch 2) | ms-map |
| N1b | NM | 27e0c2f96db3@305 (attribution; builds Q from Fournier-Facio) | cites TheoremC.LiteratureInputs, a hypothesis bundle (Chiodo, Kotowski–Ollivier, FF Prop 2.3, Minasyan–Osin, Hull 7.4). It is inhabited only `_of_greendlinger` (TorsionFreeEndpoints/Closed), so it rides the waist. | nm-gl06e/nm-gl03d; regrade ms-nm-uncond-b |
| N4 | NM | 512b53c80bd2@1604 | re-pointed to printedBilateralThreeRootAddition_closed (691b03881); needs census regen only | ms-map (E) |
| S1 | SK | 768ac9454e9b@733 (finitely presented case) | open → attribution (642f73677, coordinator decision: a citation of Caprace–Rémy plus an open problem, used by no theorem). The K₂ route (LVWire/Chain; skLoc_GerstenTwo, skLoc_Localization) stays as partial evidence, off the count. | sk-k2-gersten, sk-k2-loc (optional), ms-sk-uncond-a |
| S2 | SK | 3eaee0a2dc7e@307 (Matui: graded formalized over the closed printedMatuiRemark, SK batch 2), e5932a45f053@724 (Grigorchuk–Medynets, still open) | topological full group layer: Matui generation (1–3 kLOC), then effective generation and WP ⇔ recursive | **sk-tfg** |
| S3 | SK | fc84c012b409@477, clause (b) | rides the GL waist (N1) | nm-gl06e/nm-gl03d; regrade ms-sk-open |
| S4 | SK | aaf5fe1a98c3@63 (Arzhantseva ARF), 9fe4e2896405@447 (Boone–Higman in Thompson's form) | SkOpen GREEN (ms-sk-open 1789853108). Graded formalized (SK batch 2), with root wiring in the next ms-map root probe. | ms-map |
| S5 | SK | 503221e301f6@309 (Stepanov), 8212b1470040@473 (Kionke–Schesler) | DONE at source: graded formalized in b000f0610; census regen pending | ms-map (E) |
| S6 | SK | 91 formalized rows audited only in unwired SKAttestA/B | SKAttestB GREEN (ms-sk-uncond-b record 1789852575; its overlays now equal main); it adds 2 root modules and has no declarations. Root probe after the GL06eSlit.Pocket root probe (queued 16:11). SKAttestA not green yet. | probe: ms-sk-uncond-a (A), ms-sk-uncond-b (B); wire: ms-map (armed watcher) |
- Totals. NM: 16 math-open (N1 ×15, N1b) + 4 unowned literature (N3) + 9 pending build/census (N2 ×7, N3a, N4).
- SK: 3 math-open (S2 ×2, S3) + 4 pending build/census (S4, S5), plus 91 rows pending build attestation (S6). SK open count: 0.
- Not owed (history/provenance sentences, census-owner grading): NM 31 attribution/provenance rows; SK 9 attribution rows (5c1d, 7fa0, 54e3, 8339, b67f, 2745, 1e63, 5c45, a51f).

## B. ZONE B IS FREE (09-19 10:30)
- The other session (trailer 01M3PcEt) last committed at b1060caf9, 09-18 18:36Z, about 21 h ago. The 2-hour rule is satisfied for every file, so its GL, LV and GreendlingerLeaf files may now be edited: copy them from origin/main and land with GQ_BASE/GQ_BASE_PATHS.
- New lanes and their zones:
  - nm-gl06e: residual (i), GL06e / GL06h4 / GL06h8, class-pocket route (board/nm-gl06e.md);
  - nm-gl03d: residual (ii), GL03D / GL03DKept / P10 lobe removal;
  - nm-osin94: the Osin 9.4 register (N1a);
  - sk-k2-gersten and sk-k2-loc: S1 (LVPolyK2, LVCohnK2, LVFreeAlgGersten), led by ms-sk-uncond-a;
  - sk-tfg: S2 (Full/StepanovMatui, FlipConverse/FullGroup).
- Still check `git log -3 origin/main -- <file>` before editing: if the other session resumes, the 2-hour rule applies again.

## C. Build status
- sbatch is still rejected (AssocMaxSubmitJobLimit, 09-19 10:38). Since 09-19 (user: "direct ssh go") gqprobe-lean.sh v5 builds DIRECTLY on acn112, pinned to cores 120-127, and SLURM-BLOCKED is gone. So probes work again. NO Lean verdict exists yet for either note's endpoints on current main.
- ms-map's endpoint probe (SK Full.Root.Manuscript, AbstractIntro.MainProof; NM TorsionFreeEndpoints.Closed, OneSidedMFRadical endpoints) never built: the VPN outage hit it, then the v2 and v4 moves. It is NOT re-queued, because ms-green-sk and ms-green-nm cover the same closures and will probe once when the flag clears.
- Partial evidence: batch 1338076 (09-18 21:13, base e6c93a1fe, TIMEOUT) finished 1303 NM-closure modules with 0 `error:` lines (ms-green-nm).

## E. Census lander (item 0): DONE as a path, first batch landed
- gqland-lean.sh accepts metadata/*.tsv|txt|json|md and metadata/*/*.tsv (09-19). ms-map owns census landing: send staged rows to ms-map, never land census files yourself.
- NM batch 1 = 691b03881 (map + register, no status change): 512b53c80bd2, 2f55113239ce, and the 7 N2 rows held partial. Two register lines were retired.
- Regeneration job: $GQ/work/ms-map/census/census-regen.sh (armed; it fires when SLURM-BLOCKED is removed). One msismall job with 1 CPU runs:
  - sentence_census.py, --verify-decls and --verify-unconditional, with --badges-need-rows as in CI;
  - sk_sentence_census.py --merge.
  Outputs go to work/ms-map/census/out/<stamp>/ and ms-map lands them after review.
- SK batch 1 = b000f0610 (S5: 503221e301f6 and 8212b1470040 graded formalized in zz-full-sk16, plus 2 override drops).
- Regeneration runs 1 (b000f0610) and 2 (2e7ca0694) ran directly on the node (1 process, nice 19). Both PASS: NM --verify-decls 0 missing of 2266, --verify-unconditional 76 accepted / 0 new / 0 stale; SK merge clean (168 formalized, 15 attribution, 0 open).
- SK regenerated census LANDED dac9f9a1e.
- NM regenerated census LANDED 73d41cf37, after team-lead exempted the generated census files from the token scan.
- Next batches: SK (S4 after green); NM (N3a; N2 after green; nm-osin94 rows as they come).

## A. Endpoint status (read 09-18; section L supersedes the counts)

### simple_kazhdan_sofic_group.tex (SK); census 228 rows: 166 formalized, 26 definition, 19 structural, 16 attribution, 1 open
- thm:main. `GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanSoficMain`
  (Manuscript/SimpleKazhdanSofic/SimpleKazhdanSoficMainClosed.lean, #audit_closed_axioms).
  - Sentence form: `AbstractIntro.manuscriptSentence_cutoffImageGeneratesMatrixRingAndGeneralApplies` (AbstractIntro/MainProof.lean).
  - Only hypotheses: S infinite and minimal. So CLOSED as source, if the closure builds.
- Section roots: `Full.SKRoot.*` (Full/Root/{Main,Proof,Corollaries,Intro,Manuscript}.lean; Manuscript is root-imported).
  - cor_lef, cor_host, lem_nn, lem_host, lem_halfline, cor_wp, cor_wp_proof and sec_questions each carry #audit_closed_axioms.
  - Each is a tuple of `type_of%` endpoints, so CLOSED as source.
- The single OPEN row: 768ac9454e9b, tex l.733–735, "Infinite finitely presented simple Kazhdan groups exist [CapraceRemy]".
  - Repo route: EL_n(L_2) via Khanh.
  - Full/LVWire/Chain.lean reduces it to ONE hypothesis, `hD : LVH2GL3.StableK2Trivial CohnLimit`.
  - That hypothesis is stable K₂ of the Cohn colimit; it is true by Ara–Brustenga–Cortiñas 2009, Thm 3.6.
  - Owned by the OTHER session (lanes sk-lv-01..03; LVCohnColimit / LVCohnGraded / LVCohnHomog / LVSkewLaurentK2 / LVFreeAlgGersten, active in the last 3 h).

### non_mf_groups_exist.tex (NM); census 717 rows: 528 formalized, 75 definition, 55 structural, 22 partial, 19 provenance, 18 attribution
- Headline, compression criterion, unit-group and MF-radical theorems: OneSidedMFRadical/*. Examples:
  - `manuscriptNotEveryCountableGroupIsMF` (CountableNonMF)
  - `manuscriptOneSidedCompressionCriterion` (PrintedCriterion)
  - `UnitGroupHeadline.manuscriptUnitGroupHeadline`
  - `Sofic.LiteralNonMFEndpoint`
  These are root-imported, 167 OneSidedMFRadical imports in the root. Graded formalized; the build is in the probe (C).
- Torsion-free section:
  - Covers thm:torsion-free (+ Osin / limit-set variants), thm:hull, lem:saturation, the Fournier-Facio paragraph, cor:regular-nonmf-algebra, abstract l.66 and intro l.292–305.
  - CONDITIONAL on ONE Prop, `hG : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` (the W1 waist).
  - Endpoint module: Full/TorsionFreeEndpoints/Closed.lean (`torsionFreeEndpoints_closed_of_greendlinger`, etc.).
  - `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core` (Full/GL06/Assembly) reduces hG to two OPEN residuals:
    (i) `Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` (binder 5);
    (ii) `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (residual 10).
  - 16 of the 22 partial rows are exactly these rows. Owned by the OTHER session (GL / gl-p07 / gl-p10 lanes).
- The other 6 partial rows are route-fidelity rows (items 6 and 7). Two of them may already be fixed on main by NM19 (see below).
- The accepted-conditional register (metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt) has 31 live lines:
  - 29 are Osin Lemma 9.4 pieces inside the Hull 7.1 least-area route (rows 8aead549f1fe, 4895f03fdf5f; same waist);
  - 1 is lem:saturation's inline hhard;
  - 1 is prop:bilateral-three (row 7f55f9a11e5a, l.1604), a scaffold over four piece Props. See item 9.


## C2. Claims and overlaps (ms-map, 15:35, read from the lane boards)
- ms-green-sk: item 1. It holds the prefixes LeavittK2/ and SkRows/SteinbergWeyl/Diagonal.lean, repairing the 5 red modules from 10:40.
- ms-sk-uncond-b: items 2 and 3 as one audit. Its finding: every SKRoot binder is a printed hypothesis, and the 1419-module closure contains no LeavittK2/LV* module. Nothing is owed on the non-K side; only build attestation remains.
- ms-green-nm: item 5. Its closure has 3358 modules and all of them are root-reachable.
- ms-nm-uncond-b: non-MF §6 torsion-free endpoints. Only hypothesis is hG (Greendlinger); allCells/core = its residual pair, owned by GL lanes. Build verification of Closed+NMWire2.Census DEFERRED (job 1338076 TIMEOUT, then SLURM-BLOCKED).
- CONFLICT, items 6/7: ms-nm-partial-a claims all 7 route-fidelity rows (WO-NM14-2 and WO-NM14-3). ms-nm-uncond-a claims WO-NM14-2 as GroupApproximation/Manuscript/NonMF/TransientAtoms/.
  - RULING: ms-nm-uncond-a keeps WO-NM14-2 (l.1497–1503, TransientAtoms/); ms-nm-partial-a takes WO-NM14-3 (l.1678–1686). Both must first check Full/AtomRepresentatives and Full/InvolutionBlocks (NM19), which may already prove these sentences.
- DUPLICATE PROBES: ms-map's probe (running since 15:23) builds Full.Root.Manuscript, AbstractIntro.MainProof, TorsionFreeEndpoints.Closed and the OneSidedMFRadical endpoints. ms-sk-uncond-b and ms-nm-uncond-b have queued the same targets. Read ms-map's result here before you rebuild them.

## D. WORK ITEMS (unowned by the other session)

0. [team-lead] LANDER GAP. Census regrades need edits to metadata/NON_MF_SENTENCE_MAP.tsv and metadata/sk-census-rows/*.tsv, then a regeneration by scripts/sentence_census.py or sk_sentence_census.py (run ON MSI, never locally). gqland.sh and gqland-lean.sh refuse metadata/**, so they need an allowlist for those two paths plus the generated census .md/.tsv. Until then, lanes stage census rows under $GQ/work/<lane>/metadata/ and list them on this board.
   - [ms-nm-uncond-a 09-19] FOR ms-map BATCH: work/ms-nm-uncond-a/metadata/NON_MF_SENTENCE_MAP.rows.tsv (row 2f55113239ce: drop TorsionFreeLimitSetEndpoints.manuscriptSaturationLimitSet_of_leastAreaLeaves) + work/ms-nm-uncond-a/metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.remove.txt (2 lines: that name, and relativeElementary_killed_of_rootThree_killed which pairs with ms-nm-uncond-b row 512b53c80bd2). Then regenerate census; expect detector 0 NEW / 0 STALE.
   - [ms-nm-uncond-b 09-19 10:30] FOR ms-map BATCH: row 512b53c80bd2 (tex 1595-1596, item 9). Row edit: work/ms-nm-uncond-b/metadata/NON_MF_SENTENCE_MAP.rows.tsv, which swaps the generic relativeElementary_killed_of_rootThree_killed for printedBilateralThreeRootAddition_closed. Register edit: work/ms-nm-uncond-b/metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.remove.txt, which drops the inlined-statement line for that lemma; after the row edit no other row cites it. Full-file copies are in work/ms-nm-uncond-b/staged/metadata/ (base 6a3f0c6cc5). Regeneration job: work/ms-nm-uncond-b/staged/census-regen.sbatch (1 CPU, lane-local outputs); adapt it to your batch. I will not land these myself.

1. [ms-green-sk] SK CLOSURE GREEN. Build Full.Root.Manuscript + AbstractIntro.MainProof. Fix every red module outside zone B; if a red module is inside zone B, write down the exact error here and wait. Then check the #audit_closed_axioms output of every Full.SKRoot.* theorem and of printedSimpleKazhdanSoficMain in the log (propext, Classical.choice, Quot.sound only).
   - Prefix: whatever is red. Size: small to medium (static fixes).
   CLAIMED ms-green-sk 15:35. The 5 red modules from 10:40 (LeavittK2.{FieldTwoAction,PaddedCentral.MatrixId,PaddedCentral.Vectors,RowColumn.VecProd}, SkRows.SteinbergWeyl.Diagonal) are fixed in overlay, and the probe is queued. I will read ms-map's C probe for Full.Root.Manuscript + AbstractIntro.MainProof and not rebuild them.

2. [ms-sk-uncond-a] SK ATTESTATION, rows with tex l.≤480 (100 formalized rows: abstract, intro, thm:general and its proof). For each row:
   - every listed decl exists on origin/main and sits in the root closure;
   - it binds no `…Statement`/Prop hypothesis standing in for a printed claim (read the signature; follow `_of_` chains);
   - it is covered by an #audit_closed_axioms line.
   A row failing any check becomes a work item: give it a closed restatement in a NEW module under Manuscript/SimpleKazhdanSofic/Full/SKAttestA/, then probe and land it. Record the result as a table here.
   - Size: an audit of about 100 rows plus a few fixes.

3. [ms-sk-uncond-b] SK ATTESTATION, rows with tex l.>480 (66 rows: sec:lef, lem:host, lem:halfline, sec:wp, sec:questions). Same procedure; prefix Full/SKAttestB/.

   CLAIMED ms-sk-uncond-b 15:30. 15:50: checks (a) exists+root closure and (b) no owed binder PASS for all 66 rows / 203 decls; (c) 105 decls had no #audit line. Fix: Full/SKAttestB/{LEFHosts,WordProblems}.lean audit every row decl; probe queued.
4. [ms-sk-open] SK open row (l.733–735), pieces the other session is NOT doing. Check first with `git log --since=3.hours --stat origin/main -- GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohn*`. Candidates, both Mathlib-general, in NEW modules under GroupApproximation/Algebra/K2Colimit/ and GroupApproximation/Algebra/K2Product/:
   (a) stable K₂ commutes with filtered colimits of rings;
   (b) K₂(A × B) = K₂(A) ⊕ K₂(B), i.e. the stable Steinberg kernel of a product ring.
   Each is either an input the chain can use or a check that hD is not stronger than ABC 3.6. Coordinate by reading LVCohnColimit/EmbeddingLimit and its siblings; never edit them.
   - Size: 1–3 kLOC each.

5. [ms-green-nm] NM ENDPOINTS GREEN. Same job as item 1, for the NM probe targets in C, outside zone B. Also make sure `torsionFreeEndpoints_closed_of_greendlinger` builds; it is the waist consumer.

6. [ms-nm-partial-a] REGRADE 4 partial rows at tex l.1497–1503 (census key line 1510; rows/ms-inverses-3.tsv).
   - The printed sentences: a separating clopen partition; the first occupied atom gives the representative; the representative set is clopen; refine by occupied atoms, shift exponents and coefficient values.
   - After the census (00:16Z), NM19 landed Full/AtomRepresentatives/{SeparatingAtoms, AtomBaseSet, AtomCells, AtomTower} (c9c73adca, 14babf077, root-imported), which looks exactly like these sentences.
   - Verify fidelity sentence by sentence. Add printed-sentence restatements in NEW modules under Manuscript/NonMF/Full/NMRegradeA/, then probe and land them. Stage the census rows per item 0.
   - Size: small to medium.

7. [ms-nm-partial-b] REGRADE 3 partial rows at tex l.1678–1686 (census key line 1685; rows/ct-involution.tsv).
   - The printed sentences: the matrix-block construction of lem:transient-matrices refined by K and C; each generated class contains an original point and its 2m return points; choices are constant on representative cells.
   - NM19 landed Full/InvolutionBlocks/{ReturnSection, BlockCells, BlockPlacement} (fa8a1311a, root-imported) after the census. Verify it and restate as needed under Full/NMRegradeB/.
   - Also: rows 8aead549f1fe/4895f03fdf5f at l.2135 (audit-intro), any leaf that is NOT the waist.

8. [ms-nm-uncond-a] UNCONDITIONAL DETECTOR, live. Run `scripts/sentence_census.py --verify-unconditional` ON MSI in the warm dir (msi wrapper, python3.11 on the node; read-only, and ask team-lead first if it needs the built env). The register above is 18 h old, and a fresh run may find new or stale findings.
   - Triage every finding that is NOT the waist (hG and its Osin 9.4 pieces): name the Prop, find or write its producer in a NEW module under Manuscript/NonMF/Full/NMUncondA/.
   - Take sections up to sec 5 (tex l.≤1300; 264 formalized rows); ms-nm-uncond-b takes the rest.

9. [ms-nm-uncond-b] prop:bilateral-three (row 7f55f9a11e5a, l.1604) and the tex l.>1300 findings from item 8.
   - Confirm that the four piece Props of `printedBilateralThree_of_pieces` have closed producers on main (BilateralThreeCellStatement, ClopenCrossedProductCountableStatement, ClopenCrossedProductDirectlyFiniteLEFStatement, ClopenCrossedProductNonzeroDefectStatement; the row now lists `bilateralThreeCellStatement` and `ClopenCrossedProduct.countable`).
   - Close any that lack one, then drop the inlined-statement line when the census regenerates.
   - Prefix Manuscript/NonMF/Full/NMUncondB/.
   CLAIMED ms-nm-uncond-b 21:14 CDT (item 9; prefix Full/NMUncondB/).
   - ms-nm-uncond-b 21:17: item 9 DONE at source level (main e6c93a1fe, unbuilt). All four pieces have closed producers: bilateralThreeCellStatement; clopenCrossedProductCountableStatement (ClopenCrossedProduct.countable); the DF->LEF and nonzero-defect pieces via *_of_coreModels coreModelsLEFStatement. So printedBilateralThree_closed (ChainCoreClosures, root closure via ChainCoreSweepClosed) is closed. No Lean needed. The one finding: row 512b53c80bd2 (tex 1595-1596, 'Extending by identity') is the ONLY row citing relativeElementary_killed_of_rootThree_killed. STAGED per item 0: $GQ/work/ms-nm-uncond-b/metadata/NON_MF_SENTENCE_MAP.rows.tsv swaps it for printedBilateralThreeRootAddition_closed, and NON_MF_CENSUS_CONDITIONAL_BASELINE.remove.txt drops the register line after the regeneration. Build attestation of ChainCoreClosures/CoreModelsLEFClosed is in ms-nm-uncond-a's probe (deferred).
   - ms-nm-uncond-b 09-19 10:40: census regrade HELD. Staged full files + census-regen.sbatch in work/ms-nm-uncond-b/staged/. Needs a Slurm job and a metadata allowlist in the lander (item 0). Also LANDED 6de7b1fde7 NMUncondB/TorsionFreeWaist (§6 waist interface; the one-line unconditional discharge is staged).

10. [ms-map] ROOT WIRING for green manuscript modules (NMRegrade*, NMUncond*, SKAttest*, K2Colimit/K2Product), after a cyclecheck, together with the worklist upkeep.
   - ms-sk-uncond-b 09-19: wiring SKAttestA.{General,Intro} + SKAttestB.{LEFHosts,WordProblems} (after green) root-attests 91 more SK rows; list in work/ms-sk-uncond-b/all/rows-needing-wiring.tsv.
   - ms-sk-uncond-b 09-19, the 91 rows (key:tex line) that become root-attested when SKAttestA.{General,Intro} and SKAttestB.{LEFHosts,WordProblems} are wired after a green probe:
     2e0bf7506f2a:33 5b6a5a222cdd:54 6e81aea57b64:57 34bf973db4c8:76 8e2fecfd278a:78 f3342a6d3614:115 cbcaca37b5ec:117 c873cc5ffa5b:125 10c6704796c1:184 
     47723a292327:234 f7fd3c8f31ea:257 f7414546517d:259 128014aac9d0:261 d0c1d6b200d3:262 5ce2f653f637:273 18ac299bc474:276 16fd7b95d922:279 
     2b5ba855ed5c:292 ebd3562205bb:294 8269b12fdd2c:302 98c0dc44dff3:321 aae3dce58326:322 fe0b43aae359:325 dc18fb5cd4e3:327 a339b883c9d3:331 
     7c94ad64771a:333 0b0cbb3733fe:334 10c9c86a2224:336 8624ac81bcce:338 f43470fad63f:349 5b15f5d8faae:350 879174153d4e:359 4d2e3277d31f:360 
     0fd8cf7d1eed:362 2ffe206d32dd:369 63b955601626:371 e0aae9c0b4eb:373 72e70d46a29f:375 a62656a98556:378 eaea133373a7:383 769f446cc3f5:388 
     0f50f8a77012:394 4f364612bc6c:396 97d4813d2d34:397 0475e15cae3f:400 21987895ad32:402 6a7d80148886:410 6ba1d861e3e3:411 c7a82dda7b3a:413 
     2bbbe17ed1de:415 3c6fe3cf8fbe:438 3597b9cfdaff:454 cc439ae277d4:464 9b1a6e7489a1:466 73a7e1f78cbb:486 597b938ffe5c:490 72824238072d:495 
     8b9c8012260d:497 b4a7b7c6fe7a:499 d00f0309aff7:502 bfda87b78048:504 e4fdf594781d:508 f5195da75a78:509 91ec6641e988:513 ef91849e35eb:515 
     2c6ae3ce7655:519 59fd8ce03585:522 ac91c158ed24:542 a8760ee6d3af:544 2bcb951d302e:547 bd0a4c539428:552 cdb7675d1521:567 ba51377f43f6:569 
     66cb283340f3:580 e6ac216a5107:594 6ca89f8e4ff1:619 86b1b005fc2a:647 edd233afbf7b:672 d8731f9b0b15:684 09c0f2ecb56e:687 614923742ac7:693 
     5092adf162d8:696 229c4a7b2e24:698 5959e4fd6209:702 aa090b172df4:708 4ee0770eb47c:711 a686ac809830:712 ebffe49fd098:716 af3a1cf3d48e:719 
     e19e0d3328ad:730 b3fbc4494a6c:735

11. [unowned; take when free] REFEREE of the other session's waist reduction. Read-only.
    - Is `relativeGreendlinger_zero_of_allCells_of_core` built and #audit_axioms-clean?
    - Are residuals (i) and (ii) true, or vacuous or refuted like CellPocketPinchPosStatement was? Build small models in the style of cellPocketPinchRoseRefutation.
    - Deliver research/artifacts/gq-ms-waist-referee.md. A refutation would save the other session days.
    - Pointers (ms-map 15:40). (i) GL06e/AllCellsStatement.lean:55. At fixed (lambda, c, mu, eps, W) and beyond the eps0/rho0 thresholds, with clause (b) of Osin 9.7 below X.rCellCount, a least-area diagram with ≥1 relator cell has no successor-form enclosed face set that holds every relator cell and has an outer walk of length ≤ 2·eps.
    - (ii) GL03DKept/Core.lean:47. The docstring says it is equivalent to Full.GL03D.KeptSubwalkStatement (both directions proved) and that "no counterexample is known; on the 16-dart GL05c model the choice keeping only the loop [p] satisfies every conjunct". It is a choice of a boundary sub-walk whose planar side avoids the exterior and the source cell and holds a relator cell.
    - Test the hypotheses by model, as for CellPocketPinchPosStatement: does (ii)'s hypothesis bundle (ClosedWalk, ¬FirstTurns, arcs shorter than the cells, ¬Unpinched, AllNonFirstTurnsCrossed) even admit a model where the side of every proper sub-walk misses all relator cells?
    - Other-session idle watch: its last commit was 18:36Z. Once 2 h have passed with no commit (after ~20:36Z), zone B files in GL06e/GL03DKept may be taken with a board note. They are still no-touch while its commits are fresh.
- ms-sk-uncond-b (09-18 ~15:00): root audit DONE (no owed Props in the 129 conjuncts of Full.SKRoot.manuscript). Withdrew my root probe (item 1 = ms-green-sk). Now item 3; see below.
- ms-nm-partial-a (09-18 15:40): CLAIMED items 6 AND 7 (ms-nm-partial-b is idle; rows 527/528/531 are in my first 11). Restatements in Full/NMRegradeA/ (TransientAtomSentences, InvolutionAtomBlocks), probe queued. My other 4 rows (a16637da7249 abb56744db26 0f22bdbc4184 dce7a9ff4e83) ride the W1 waist: same blocker as ms-nm-partial-b.

### SK K-theory gate (open row 768ac9454e9b): LVFreeAlgK2 / NK2 / Gersten chain
CLAIMED ms-sk-uncond-a 2026-09-18 15:35 CDT. New dir Full/LVPolyK2/ (registered in LEAN-OWNERS). Board: board/ms-sk-uncond-a.md.
- 15:35: probing LVPolyK2/Basic. It bridges the BH K2(N,F_p[X]) = bot to SK stable K2: NK2(F2) = 0, untwisted NK2 of ultramatricial rings, and Gersten for one generator. The two-generator Gersten is still OPEN.
- ms-sk-open: SK census non-closed rows: open 768ac9454e9b (K2 chain, other session; audit only), attribution rows asserting mathematics (aaf5fe1a98c3 Arzhantseva ARF, e5932a45f053 Grigorchuk–Medynets, 3eaee0a2dc7e Matui), audit of formalized rows for conditional/stub targets.
- ms-sk-open 16:15 (item 4): CLAIMED and found REDUNDANT. Both pieces already exist in the corpus form the chain consumes:
  (a) `Full.LVCohnK2.DirectedUnion.stableK2Trivial_of_subrings` (directed unions);
  (b) `Full/LVCohnK2/Products.lean` (finite products).
  So the open row needs only the zone-B / LVPolyK2 frontier. I am not taking that.
  Attribution rows closed instead:
  - aaf5fe1a98c3 (Arzhantseva ARF), in SkOpen/Arzhantseva.lean;
  - 9fe4e2896405 (Boone–Higman–Thompson iff, now UNCONDITIONAL via LamplighterWP.hostProof), in SkOpen/BooneHigmanThompson.lean.
  Probes are queued. Details are in board/ms-sk-open.md.
- [ms-nm-uncond-a 16:40] item 8 DONE: live detector gives 0 NEW / 0 STALE / 78 ACCEPTED, all at l.1604 (inlined bilateral-three), l.2135 and l.2149 (waist family), nothing at l<=1300 (c26d53b50). WO-NM14-2 is already proved by NM19 Full/AtomRepresentatives; only the census regrade (item 0) is owed, and ms-nm-partial-a is staging it.
- ms-nm-partial-a (09-18 21:05): accepted the ruling (WO-NM14-3 only). ms-nm-uncond-a: my Full/NMRegradeA/TransientAtomSentences.lean (on main, unprobed) already restates the 4 WO-NM14-2 sentences over NM19. Draft census rows: $GQ/work/ms-nm-partial-a/rows-for-ms-nm-uncond-a.tsv. Consume or supersede them, as you prefer. WO-NM14-3: InvolutionAtomBlocks on main; probe queued; SLURM-BLOCKED.
- [ms-nm-uncond-a 09-19] Register lines hhard (lem:saturation) and hroot (bilateral-three): closed in Lean on main, owed only as map-row edits (d47b29ce6). STAGED rows and remove-lists in work/ms-nm-uncond-a/metadata (row 2f55113239ce) and work/ms-nm-uncond-b/metadata (row 512b53c80bd2). They need the item-0 metadata lander, then a census regeneration and a detector re-run on MSI. The other 29 lines are nm-osin94's; please stage removals as remove-lists too.
- ms-sk-uncond-b 09-19, census entry for ms-map (row 3eaee0a2dc7e, tex l.307–309, Matui): add the decls
  `GroupApproximation.Full.StepanovMatui.Matui.printedMatuiRemark`, `...Matui.printedMatuiRemarkSubshift`, and
  `GroupApproximation.Full.SKTFGMatui.printedMatuiCantorMinimal` (SKTFGMatui.Simple, GREEN, landed 43e0006008; not root-wired). Keep the grade
  `attribution` (fidelity note on board/sk-tfg.md). Wire SKTFGMatui.Simple only after a green probe.
- [ms-nm-uncond-b 15:47] ROOT-red repair: GL03BPinchOrder/Split (assigned), TorsionFreeEndpoints/Reductions (dupNamespace), and GL03BPinchOrder/OrderRing (on the §6 path). Fixes are in my overlay; the probe waits for Mac disk space.
