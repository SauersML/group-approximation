# MS-WORKLIST: formalize both manuscripts unconditionally (owner ms-map; v1 2026-09-18 ~15:05 CDT)

Source of truth: origin/main at c7f12fba7 (read, not built), plus the ms-map probe (section C, pending).
Both censuses are current with their tex (SK: md5 d41890ab; NM: SHA-256 36350917), so their rows match the printed sentences.
Claim an item by appending `CLAIMED <lane> <time>` under it. Record progress lines under the item.

## A. Endpoint status

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

## B. OTHER-SESSION ACTIVE ZONES (session trailer 01M3PcEt; 224 commits in the last 6 h). DO NOT EDIT; consume only.
- GroupApproximation/GGT/VanKampen/GreendlingerLeaf/**. P07InnerPocket had 57 files touched, Piece10Live 49, P10RoseLobe 48; also P06Rose*, P10Quadrant*, P10Blk*, P10Walk*, Piece07Below, and others.
- Manuscript/NonMF/Full/{GL03BPinchOrder, GL06*, GL03DKept, GL03CRetire, NMWire, NMWire2, TorsionFreeEndpoints}
- Manuscript/SimpleKazhdanSofic/Full/{LVSkewLaurentK2, LVCohnColimit, LVCohnGraded, LVCohnHomog, LVFreeAlgGersten, LVWire, SKFix01}, LeavittK2/CohnTwo
- BooneHigman/Metabelian/** (bh-met lanes)
Before editing ANY existing file, run `git log -3 --format='%h %ci %s' origin/main -- <file>`; anything under 2 h old from that session is off limits.

## C. Red modules (ms-map probe of the endpoint modules on MSI, empty overlay)
- Probe queued at 14:50 behind bh-pal-integrate. Targets:
  - SK: Full.Root.Manuscript, AbstractIntro.MainProof;
  - NM: TorsionFreeEndpoints.Closed, OneSidedMFRadical.{UnitGroupHeadline, PrintedCriterion, CountableNonMF}, Sofic.LiteralNonMFEndpoint, ClosureAssumptionAudit.
- 15:23 run: FAILED at the source rsync (rc 255, "unexpected end of file"). This was the 15:26 VPN/DNS outage; nothing was built, so it says nothing about Lean. Re-queued at 15:34 (same targets, empty overlay).
- Result: PENDING.
- Prior evidence (bh-pal-wire, 10:40, main 505b3b720): 5 hard-red modules under Manuscript/SimpleKazhdanSofic inside the BH FrontierFour closure.

## C2. Claims and overlaps (ms-map, 15:35, read from the lane boards)
- ms-green-sk: item 1. It holds the prefixes LeavittK2/ and SkRows/SteinbergWeyl/Diagonal.lean, repairing the 5 red modules from 10:40.
- ms-sk-uncond-b: items 2 and 3 as one audit. Its finding: every SKRoot binder is a printed hypothesis, and the 1419-module closure contains no LeavittK2/LV* module. Nothing is owed on the non-K side; only build attestation remains.
- ms-green-nm: item 5. Its closure has 3358 modules and all of them are root-reachable.
- ms-nm-uncond-b: section 6 partial rows. Each is partial ONLY through hG (Hull 5.7, 5.8, 3.5 and the bridge are closed).
- CONFLICT, items 6/7: ms-nm-partial-a claims all 7 route-fidelity rows (WO-NM14-2 and WO-NM14-3). ms-nm-uncond-a claims WO-NM14-2 as GroupApproximation/Manuscript/NonMF/TransientAtoms/.
  - RULING: ms-nm-uncond-a keeps WO-NM14-2 (l.1497–1503, TransientAtoms/); ms-nm-partial-a takes WO-NM14-3 (l.1678–1686). Both must first check Full/AtomRepresentatives and Full/InvolutionBlocks (NM19), which may already prove these sentences.
- DUPLICATE PROBES: ms-map's probe (running since 15:23) builds Full.Root.Manuscript, AbstractIntro.MainProof, TorsionFreeEndpoints.Closed and the OneSidedMFRadical endpoints. ms-sk-uncond-b and ms-nm-uncond-b have queued the same targets. Read ms-map's result here before you rebuild them.

## D. WORK ITEMS (unowned by the other session)

0. [team-lead] LANDER GAP. Census regrades need edits to metadata/NON_MF_SENTENCE_MAP.tsv and metadata/sk-census-rows/*.tsv, then a regeneration by scripts/sentence_census.py or sk_sentence_census.py (run ON MSI, never locally). gqland.sh and gqland-lean.sh refuse metadata/**, so they need an allowlist for those two paths plus the generated census .md/.tsv. Until then, lanes stage census rows under $GQ/work/<lane>/metadata/ and list them on this board.

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

10. [ms-map] ROOT WIRING for green manuscript modules (NMRegrade*, NMUncond*, SKAttest*, K2Colimit/K2Product), after a cyclecheck, together with the worklist upkeep.

11. [unowned; take when free] REFEREE of the other session's waist reduction. Read-only.
    - Is `relativeGreendlinger_zero_of_allCells_of_core` built and #audit_axioms-clean?
    - Are residuals (i) and (ii) true, or vacuous or refuted like CellPocketPinchPosStatement was? Build small models in the style of cellPocketPinchRoseRefutation.
    - Deliver research/artifacts/gq-ms-waist-referee.md. A refutation would save the other session days.
    - Pointers (ms-map 15:40). (i) GL06e/AllCellsStatement.lean:55. At fixed (lambda, c, mu, eps, W) and beyond the eps0/rho0 thresholds, with clause (b) of Osin 9.7 below X.rCellCount, a least-area diagram with ≥1 relator cell has no successor-form enclosed face set that holds every relator cell and has an outer walk of length ≤ 2·eps.
    - (ii) GL03DKept/Core.lean:47. The docstring says it is equivalent to Full.GL03D.KeptSubwalkStatement (both directions proved) and that "no counterexample is known; on the 16-dart GL05c model the choice keeping only the loop [p] satisfies every conjunct". It is a choice of a boundary sub-walk whose planar side avoids the exterior and the source cell and holds a relator cell.
    - Test the hypotheses by model, as for CellPocketPinchPosStatement: does (ii)'s hypothesis bundle (ClosedWalk, ¬FirstTurns, arcs shorter than the cells, ¬Unpinched, AllNonFirstTurnsCrossed) even admit a model where the side of every proper sub-walk misses all relator cells?
    - Other-session idle watch: its last commit was 18:36Z. Once 2 h have passed with no commit (after ~20:36Z), zone B files in GL06e/GL03DKept may be taken with a board note. They are still no-touch while its commits are fresh.
- ms-sk-uncond-b (09-18 ~15:00): SK non-K-theory audit DONE. All 129 conjuncts of Full.SKRoot.manuscript carry only printed hypotheses, so there are no owed Props. The root closure (1419 modules) contains no LeavittK2/LeavittFP/Full.LV* and none of the 10:40 red modules. Claiming the build attestation of GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Root.Manuscript (probe queued); ms-green-sk need not duplicate it. Details: board/ms-sk-uncond-b.md.
