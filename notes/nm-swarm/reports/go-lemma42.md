# go-lemma42 (lane report, 2026-09-13, pinch-step (ii))

Item (team-lead, ~15:00): sub-piece (ii) of hull-respell's pinch-step route. Carry the pocket face set K across one
split that merges corners inside K, with K' in walk order and fewer repeated visits. The route is
`PocketPinchStepStatement` (OsinPocketPinchStep, 8a7d46d90). I asked hull-respell for its interface and had no reply,
so the interface mirrors kh-cckw's E4 (`OsinPocketPinchSplitWalk`, ceeb03ecd).

## Module `Estimating/OsinPocketPinchCarry` (unwired)
- 9acc804f2: landed unverified. Probe 0913-153115-61308 FAILED with one error: `Finset.mem_image` on `I.faceSet s`
  needs `open scoped Classical in`, as in SurgeryPinchSplitRegions.
- LANDED, green: 275e24b43. Probe 0913-153737-1399 GREEN (base 4bc730024, md5 7640a9ed, bytes = origin); every
  `#audit_axioms` prints [propext, Classical.choice, Quot.sound]. Wire-queued 09-13 after OsinPocketPinchSplitWalk.
- namespace `PinchSplit.Input`:
  - `Inside s`: `leftFace ∈ s ∧ rightFace ∈ s`;
  - `kept_mem_faceSet_iff_of_inside`, `faceOf_mem_faceSet_iff_of_inside`, `isBoundaryDart_iff_of_inside`: with both
    merged faces in `s`, a face lies in the image face set exactly when it lay in `s`, so the boundary darts are unchanged;
  - `transportBoundaryCycleInside` with `_cycle` (rfl);
  - `vertexOf_eq_of_stretchAvoids_or`: a stretch in either direction stays on one new vertex.
- namespace `PocketFaceSet`:
  - `pinchSplitInside K I hs : PocketFaceSet D eps I.diagram lo hi`, with rfl lemmas `_faces`, `_source`, `_kept`,
    `_boundary_cycle`, `_firstSide`, `_secondSide` and the arc lemmas `_sourceArc_darts`, `_targetArc_darts`,
    `_targetArc_start`;
  - `pinchSplitInside_closedWalk K I hs hchain hcloses`. Each turn is `StretchAvoids (alpha d) e ∨ StretchAvoids e (alpha d)`.
    The outer pairing at the split vertex turns against vertex rotation: the new vertex (y, x] reads e₁, gap, alpha d₂.
  - `pinchSplitInside_repeatedVisits_lt K I hs he₁ he₂ hx hy` and `_of_stretch`;
  - `exists_pinchStep_of_inside hlabel K I hs hchain hcloses he₁ he₂ hx hy`: exactly the conclusion of
    `PocketPinchStepStatement`, with `X' := I.diagram` and `K' := K.pinchSplitInside I hs`.

## Applicability and residual
- `PinchSplit.Input` requires `left_not_cell` and `right_not_cell`. Under `Inside` both merged faces lie in K, so they
  must be G-faces of K (`inner_face`, second disjunct: boundary value 1). `left_ne_outer` and `right_ne_outer` follow
  from `outerFace_not_mem`.
- RESIDUAL, for the composition (hull-respell): from a pinched K in walk order, build an `Input` with `Inside` at an
  outermost passage (`Cycles`, G-face corners), with `hchain`, `hcloses`, `e₁` and `e₂`. When a corner is a relator cell
  this needs a doubled edge (face edge doubling) first, or a different K' (kh-cckw: neither on-main pinch model has a
  G-face corner pinch).

# go-lemma42 (lane report, 2026-09-13)

Item (team-lead, after the 08:30 restart): Estimating/OsinPocketGlueDiagram, then the `htransport` of
`OsinMultipleEdgeCut.ofPocketRegion` at j = 1, 3, with FollowsBoundary as a hypothesis. That is
`PocketCellTransportStatement` (OsinPocketPieces:312). `PocketOuterTransportStatement` is hull-select's
(`pocketOuterTransport`, 71d59592c).

## LANDED, green
- 0358f4537 SurgeryPocketGlue (probe 0913-062050-80403): `Seam.glueMap`, `Seam.glue_isRestriction`.
- 3af801bac SurgeryPocketGlueCount (0913-070238-32448), 0cdb0dc87 SurgeryPocketGlueVertices (0913-072208-51095),
  291ae2c87 SurgeryPocketGluePlanar, 32116a8bc SurgeryPocketGlueFaces (0913-094529-34532). All rooted.
- f914f8728 Estimating/OsinPocketGlueDiagram, b10fac78a Estimating/OsinPocketGlueEquivalence (0913-125816-38320).
  Both rooted.
- 874a332a2 Estimating/OsinPocketGlueCarriers and Estimating/OsinPocketGlueCellTransport (probe 0913-141750-43433
  GREEN, base 874a332a2, bytes = origin). `pocketCellTransport : PocketCellTransportStatement`,
  `#audit_closed_axioms` [propext, Classical.choice, Quot.sound]. Wire-queued 09-13 14:21, Carriers first.

## The proof
- `DiscEmbeddingAway.retargetGeometry`: moves a contiguity geometry of a face set that avoids the embedded face
  along the embedding. The target is retargeted to any carrier arc that reads the images of the target darts.
- `PocketRegion.glueCellArc`: the window of the carrier arc of a complement cell `t` (not in the pocket) in the
  glued diagram. `glueCellArc_boundaryDarts` reads it as the embedded window of the outer darts of `Xi`.
- The source becomes `glueRightCell` (a relator cell of the copy) and the target `glueLeftCell t`. They differ
  because the seam faces differ (`leftFace_ne_rightFace`). The contiguity degree is kept (`mapTo_length`, and
  word lengths through `dartWord_map`).

## Consumers still carrying `hcell` (other lanes' files)
- `osinSectionPocketCutSection_of_residuals` (OsinPocketCutResiduals, dgo-analytic). With
  `hcell := pocketCellTransport`, the residuals are `OsinSectionPocketFaceSetSectionStatement` (kh-ejz),
  `PocketPinchLabelledStatement` (hull-respell) and `GeodesicCollarStatement` (kh-torsion).
- `osinMultipleEdgeCutSection_of_pieces` (OsinPocketMultipleEdgeAssembly). The residuals are
  `OsinMultipleEdgePocketRegionSectionStatement` (kh-ejz) and `GeodesicCollarStatement` (kh-torsion).
- The `htransport` of `OsinMultipleEdgeCut.ofPocketRegion` (OsinPocketMultipleEdgeCut:49) is passed as
  `fourSectionCuts_cellTransport hcell` (OsinPocketMultipleEdgeTransport:64, Assembly:172). The `htransport` of
  `OsinLoopCut.ofPocketRegion` (OsinPocketLoopCut:115) is passed as `twoSectionCuts_cellTransport hcell`
  (LoopCut:161). Both close with `pocketCellTransport`.

## TRAPS (09-13)
- Local `git grep` misses plumbing-landed files. Grep `origin/main -- paths` instead, and compare bytes with
  `git show origin/main:F | cmp - F`.
- `$NM` is not set in a lane shell. Use the full scratchpad path.
- `subst hc` with `hc : c' = outerDarts Xi` did not elaborate as intended; `subst c'` names the variable.
- A probe notification's exit code is the exit of `| tail`. Read `PROBE GREEN` in the output file.
- nmland's git gc warnings (too many unreachable loose objects) are harmless; check ancestry anyway.

# go-lemma42 (lane report, 2026-09-11)

Scope (lead correction ~21:15): take over `Manuscript/NonMF/GerasimovaOsinLemma42Proof.lean` from
dgo-geometric, make it compile, land it; no second Lemma 4.2 proof.

## State of the files
- `GerasimovaOsinLemma42Proof.lean`: origin 110ba458c (md5 80b0c6fd…); latest = attic 2b7e8298d = shared tree
  (md5 b53ff9d9…). Docstring-only change: route note, and "no census row of its own" in place of `partial`.
- `GGT/GerasimovaOsinCyclicTwoSided.lean` (dgo-geometric's, READ-ONLY here): origin 7561321b…; latest = attic
  4ac077236 = shared tree (md5 350bd666…). Repair: `Elementary.base_subset_alphabet_carrier` (outside the import
  closure) replaced by `Set.mem_union_left _` at lines 237 and 318.
- Both latest bytes are in dgo-geometric's probe 0911-210846-20111 (SLURM 435379, acn141, base 4ac077236).

## Probe results
- 0911-210846-20111 (dgo-geometric's, base 4ac077236): `GerasimovaOsinCyclicTwoSided` BUILT [9879/9879] (558s), in
  COMPILED evidence with md5 350bd666. The probe FAILED only on PNaivePingPong (outside this closure).
  `GerasimovaOsinLemma42Proof` was not in its module list: NOT built yet.
- go-lemma42 wrapper probe: queued behind nm-b preparation (background waiter, re-reads the clone assignment).

## Checked by reading
- The theorem is closed: no hypothesis left open. `HasTrivialFiniteRadical G` unfolds to exactly the `hrad`
  binder of `exists_cyclic_hypEmbedded_twoSided`. `coneOffFamily A K` has `base := A.carrier` and
  `RelGenSet.alphabet D = ⟨D.base ∪ ⋃ fam, _⟩`, so the `Set.mem_union_left` repair and `D'.base` uses are definitional.
- Imports: CyclicWord and LoxodromicCyclicEmbeddedAvoiding compiled (replayed in the probe);
  GerasimovaOsinGeometricInputs compiled (go-sr1).
- The probe's red module PNaivePingPong (sorryAx at 164) is outside this closure.

## Census
No row: Lemma 4.2 is internal to the cited proof of GO Theorem 1.1. The printed sentence (tex 1729–1731,
cor:regular-nonmf-algebra) is graded through `GerasimovaOsinTheorem11Printed`.

## LANDED
- 5558478e0 `Manuscript/NonMF/GerasimovaOsinLemma42Proof` (probe 0911-213026-69780, cs-simplicity, BUILT 43s). CyclicTwoSided
  landed by dgo-geometric at 2ec9cfdba. Lemma 4.2 is closed; nothing is left as a hypothesis.
- b8af8cb13 census merge (map, register, census tsv/md) at origin 434d65bfb: 323 formalized / 51 definition / 46 structural /
  19 provenance / 18 attribution / 36 partial / 5 unassigned. verify-decls 0 missing of 811; verify-unconditional
  189 accepted, 0 new.

## Census tooling (census/)
census_merge.sh (acn112 via msi; live work dir merge-live, delta sync), merge_rows.py (sentence start-line location,
statement-env rows, unions, compiled-evidence downgrade incl. clone oleans), overrides.tsv, baseline-merge.txt.

## TRAPS
- nmland.sh rewritten mid-run: bash reads scripts lazily, so a run printed LANDED-like output and a landed.log line
  for a commit that never reached origin. Always check `git merge-base --is-ancestor <sha> origin/main`.
- sentence_census.py records PARAGRAPH start lines; lanes' LINE:<n> keys need the sentence's own start line.
- f57b559f7 census merge step (rows from metadata/nm-census-rows, 13 lanes): unions per sentence, register.py (10 lines),
  verify-unconditional 236 accepted / 0 new. census_merge.sh lands every step (rule 21) and verifies the sha on origin.
- 0911-231324-58545 PROBE GREEN: BinaryExampleSentences, IntroSentences, KorchaginFullSequenceSentence compiled unchanged
  (bytes = origin; nothing to land). Wire candidates (0 importers).
- 91fbada58 GroupTheory/HydeLodha/QTwoBrownTriangle (probe 0912-003620-69441 GREEN): vertexH_triangle (htri for simple-group),
  exists_commutator_compactCore_move, exists_edgeStab_left, resLabel, triKey, triKey_eq.
- TRAP: `open Classical in` must precede the docstring (a docstring followed by `open ... in` is a parse error).
