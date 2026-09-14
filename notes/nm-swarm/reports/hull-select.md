# hull-select report

Lane `hull-select` of the non-MF every-line swarm (09-13).

## Target

- Roster target: a closed `MultipleEdgeCutInput`
  (`GGT/VanKampen/Estimating/OsinAppendixSectionInduction.lean:76`), stated uniformly in
  the parameters as `OsinMultipleEdgeCutSectionStatement`
  (`Estimating/OsinAppendixGreendlingerParts.lean:49`), which the root producer
  `_of_pocketParts` consumes.
- Items from the lead after the 08:30 restart:
  1. The merge Prop over disc-region data, with the target a section or a second cell. Done at
     ce1028aa1.
  2. `multipleEdgeCutInput_of_pieces` over `MultipleEdgePocketRegionInput` (kh-ejz), the
     collar (kh-torsion), the transport (go-lemma42) and the merge. Lifted over
     `OsinMultipleEdgePocketRegionSectionStatement` (ROSTER, "Pocket pieces"). Done at
     2db85602c.
- Items from the lead after the assembly:
  1. `PocketOuterTransportStatement` (`Estimating/OsinPocketPieces.lean`), a PocketCut leaf of
     dgo-analytic. Taken over from go-lemma42 (ROSTER line 737). Done at 71d59592c.
  2. After dgo-analytic fixes the carrier form (R2 or R1), restate
     `MultipleEdgePocketRegionInput` on the O-equivalent copy in one co-probe with the assembly
     (kh-ejz owns the Prop), then send jacobson the final form.
- Item from the lead (15:00): one module producing the four inputs of
  `PocketRegion.ofNoncrossingClosedWalk` (8bbf0a9c8) for non-simple pocket walks, for jacobson
  (Case 1 walk `X ++ M'`) and fff-periodic (site 5). Done at a29b02280.

## Landed

- aa1b561db, `Estimating/OsinPocketLeastAreaCut.lean`, and 3f87827d0,
  `Estimating/OsinPocketMultipleEdgeCut.lean`: the section layer and `ofRegionCut` on
  `RegionCutData`. Closed, but unused: `RegionCutData` has no producer.
- 45e7201da, `Estimating/OsinPocketRegionSections.lean` (green 0913-042552-816):
  `PocketRegion.boundarySectionCuts`, `fourSectionCuts` (+ `_count`, `_side_short`,
  `_leastAreaCut`), and `OsinMultipleEdgeCut.ofPocketRegion`, the producer of the cut from a
  pocket region of an O-equivalent copy.
- b45e7ef30: the `i ≠ j →` binder on `MultipleEdgeCutInput`, together with its two consumers
  (green 0913-042552-816).
- a4cd9934d, `Estimating/OsinPocketRegionRotate.lean`: a pocket region can start at any dart of
  its complement cycle.
- a73ab6f78 and 97a6dbe03, `Estimating/OsinPocketZeroCellMerge.lean`: the boundary and the
  merged contiguity region of a zero-cell pocket.
- ce1028aa1, `Estimating/OsinPocketZeroCellMergeFalse.lean` (green 0913-094902-38721; axioms
  propext, Classical.choice, Quot.sound; in lead-wire's wave 65d0a449):
  - `ZeroCellPocketMergeStatement` and `zeroCellPocketMerge`, closed.
  - Two selected regions `a ≠ b` and a pocket region with no relator cell, avoided by the other
    selected regions, whose inverse complement cycle reads a reversed source arc, a short side, a
    target arc (of a section or of a cell) and a short side. With nonempty arcs outweighing
    `a` and `b`, there is a contradiction.
  - Proof through `Surgery.InnerDiscRegion.ofPocketRegion` and
    `false_of_disc_collapse_singleton`. No boundary-walk hypothesis is needed, so pinched pockets
    are covered.
- 2db85602c, `Estimating/OsinPocketMultipleEdgeAssembly.lean` (green 0913-111924-29328, BUILT;
  axioms propext, Classical.choice, Quot.sound; wire-queue line 609):
  - `PocketRegion.ne_or_of_leastArea`: in a least-area diagram, a pocket with a relator cell
    inside has a nonempty arc or a side of value `≠ 1`. This is the `hne` input of the two-collar
    lemma.
  - `nonempty_osinMultipleEdgeCut_of_pocketRegion`: the cut of `Δ` from a pocket region of any
    O-equivalent copy `X` with labels in `symmetricLabelAlphabet D`. Collar geodesic words along
    both sides (`PocketRegion.exists_twoCollars_of_ne_or`, hl-lemma46, over
    `GeodesicCollarStatement`). Map the arcs with `CyclicArc.mapTo`. Take quasi-geodesic parts
    from the geodesic collar words and `OsinCCondition`. Apply `OsinMultipleEdgeCut.ofPocketRegion`
    with `PocketRegion.fourSectionCuts_cellTransport` (hl-lemma46, over
    `PocketCellTransportStatement`).
  - `multipleEdgeCutInput_of_pieces`: `MultipleEdgeCutInput` from
    `MultipleEdgePocketRegionInput`, `GeodesicCollarStatement` and
    `PocketCellTransportStatement`, under `OsinCCondition` with `λ ≤ 1`, `0 ≤ c`.
  - `OsinMultipleEdgePocketRegionSectionStatement` (the quantifier prefix of
    `OsinMultipleEdgeCutSectionStatement`, concluding `MultipleEdgePocketRegionInput`) and
    `osinMultipleEdgeCutSection_of_pieces`: `OsinMultipleEdgeCutSectionStatement` from it and the
    two statements.
- 4a4f1a6b6, `Estimating/OsinPocketGlueOuterArc.lean` (green 0913-134755-12194), and
  71d59592c, `Estimating/OsinPocketGlueOuterTransport.lean` (green 0913-134953-22063; axioms
  propext, Classical.choice, Quot.sound):
  - `PocketRegion.exists_glue_outerArc(_within)`: an outer arc of the copy `Ξ` in the positions
    `pre.length ≤ k < pre.length + arc.length` of the reversed complement cycle goes to an outer
    arc of `glueDiagram` inside `arc`, and its darts are the image darts.
  - `DiscEmbeddingAway.outerGeometry`: a region to the boundary moves along an embedding away from
    a face outside it, given an image source cell and an image target arc.
    (`contiguityGeometry` needs `f ≠ outerFace`, so it doesn't apply here.)
  - `PocketRegion.exists_glue_cell`: a relator cell of `Ξ` is a relator cell of `glueDiagram`
    with the image carrier.
  - `pocketOuterTransport : PocketOuterTransportStatement`, closed. It consumes go-lemma42's
    `glueEmbeddingAway`, `glueRight_mem`, `glueXFace_of_ne` and `glueOEquivalent`.
- a29b02280, `Estimating/OsinPocketFirstTurnWalk.lean` (green 0913-153749-2116; axioms propext,
  Classical.choice, Quot.sound; unwired):
  - `FirstTurn M c x y`: rotating from `alpha x`, the first dart that lies in `c` or reverses a
    dart of `c` is `y`.
  - `FirstTurnWalkPocketInputsStatement` / `firstTurnWalkPocketInputs`, closed. Take a planar map
    and a nonempty, duplicate-free list `c` that uses no edge in both directions, in which each
    dart reaches the next, and the last the first, by a first turn. Then the reversed walk
    `c.reverse.map alpha` is noncrossing (hull-respell's `BoundaryCycle.isNoncrossingClosedWalk`),
    no face on the side of `c` lies on its side, its outer cycle follows its boundary, and the
    reclosed Euler equality holds (hull-euler's `reclosed_euler`).
  - `PocketRegion.ofFirstTurnWalk`: the pocket region, given in addition only
    `hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c`, with its faces, cycle and `invDarts`
    lemmas.
  - Producers: `FirstTurn.of_facePerm`, `of_sigma_alpha`, `of_sigma_sigma_alpha`,
    `of_boundaryWalk`, `mono`, and `FirstTurnWalk.faceOf_mem_sideFaces` (for `hout`).
  - Sent to jacobson and fff-periodic (15:50).
- b8c0033c0, `Estimating/OsinPocketFirstTurnWalkModel.lean` (green 0913-161209-37045; axioms propext,
  Classical.choice, Quot.sound; unwired), model tests, closed endpoint
  `FirstTurnWalkModelStatement` / `firstTurnWalkModel`:
  - Configuration A: the complement spelling `[9,8,0,1]` satisfies every hypothesis and its side
    holds the exterior face. The walk it certifies, `[5,3,4,6]`, is not simple, and the builder
    gives face set `pinchFaces`.
  - The lake: the outer cycle `[3,1]` fails a first turn, as it must, since that outer cycle does
    not follow its boundary (`lakeCycle_outerCycle_not_followsBoundary`).
  - A pendant spur: the trimmed spelling `[0]` gives the four inputs. The untrimmed facial
    spelling `[0,2,3]` fails the edge condition.

## Residual Props for `OsinMultipleEdgeCutSectionStatement`

`osinMultipleEdgeCutSection_of_pieces` leaves exactly three binders:
1. `OsinMultipleEdgePocketRegionSectionStatement`, from kh-ejz. The zero-cell merge
   (`zeroCellPocketMerge`, closed) enters through this producer.
2. `GeodesicCollarStatement`, from kh-torsion.
3. `PocketCellTransportStatement`, from go-lemma42.

Notes for the producers:
- `MultipleEdgePocketRegionInput` is on an O-equivalent copy (ruling B, copy form, green 0913-173001-68048). The
  producer gives the copy `X`, `Nonempty (OEquivalentDiscDiagram Δ X)`, label legality
  `∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)`, and the pocket data on `X`. The
  side-length bounds are gone, since the collar words have length `wordNorm ≤ ε`.
- Both `FollowsBoundary` conditions stay (R1), so the pocket is simple. In audit-sec5's
  configuration (b′) the gap pocket on the copy is pinched, so the producer needs the
  cell-to-cell pinch Prop that audit-sec5 owns.

## Holds and next

- First-turn inputs: the consumers' residual is `hout` plus the hypotheses on `c`. Waiting for
  jacobson (does 61c2ade8e make the Case 1 walk simple?) and fff-periodic (the site 5 arc) to
  confirm their walks fit `FirstTurn`.
- hull-euler confirms `reclosed_euler` is final (19866c7d6). A restatement would co-probe both
  first-turn modules.
- LoopCut (A) landed at f04929ebb, including the loop-ruling version of
  `OsinPocketZeroCellMergeFalse.lean`, so the hold on the zero-cell merge files is released.
  theoremc-retire's T landed at 48c6cc71e.
- `pocketOuterTransport` closes the `houter` binder of the section pocket cut assembly
  (`OsinPocketPieces`). The cell transport `hcell` is still go-lemma42's.
- Now: item 2, the O-equivalent-copy restatement of `MultipleEdgePocketRegionInput`. Main's
  15:45 ruling, after audit-sec5's truth audit: on `S.diagram`, configuration (b′) has no `P`, so
  that form holds only through Lemma 9.7(b) itself. The R1 copy forms land through the Rule 22
  co-probe of `OsinPocketRegionSide`, `OsinPocketMultipleEdgeAssembly`, `OsinDescentResiduals`,
  `OsinDescentResidualsPos`, `OsinGreendlingerOpenResiduals` and `OsinPocketLoopCut` (green
  0913-173001-68048 on base c55730449; 0913-162107-78743 missed LoopCut and 0913-170231-58844
  missed `OsinDescentResidualsPos`). audit-sec5 owns the
  cell-to-cell pinch Prop that the producer needs, since the (b′) pocket on the copy is pinched.
  - Form: `∃ X, Nonempty (OEquivalentDiscDiagram Δ X) ∧ (∀ d, legal label) ∧ ∃ P C i' j' s₁ s₂
    A₁ A₂, …`, with both `FollowsBoundary` conditions (R1) and no side-length bounds. Sent to
    kh-ejz and, as the target form, to jacobson (14:10). kh-ejz was told before the edit (16:20).
  - Rule 22 users on origin/main: the assembly, and the pass-throughs `OsinDescentResiduals`
    (:44, :59), `OsinGreendlingerOpenResiduals` (:57) and `OsinDescentResidualsPos` (:35, :50;
    4db9c6729, landed after the first re-grep), plus jacobson's `OsinPocketLoopCut` (:219,
    `ne_or_of_leastArea`, statement unchanged). `OsinPocketCellWalk` and
    `OsinPocketMultipleEdgeLakeModel` mention it only in docstrings. Re-grepped on 46a9d16ff.
  - Backups of the pre-copy files: `$NM/backup/hull-select/*.pre-copy-0913`.
- The assembly modules are infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7)
  and certify no printed sentence on their own, so there are no census rows.
