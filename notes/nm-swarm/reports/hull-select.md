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

## Residual Props for `OsinMultipleEdgeCutSectionStatement`

`osinMultipleEdgeCutSection_of_pieces` leaves exactly three binders:
1. `OsinMultipleEdgePocketRegionSectionStatement`, from kh-ejz. The zero-cell merge
   (`zeroCellPocketMerge`, closed) enters through this producer.
2. `GeodesicCollarStatement`, from kh-torsion.
3. `PocketCellTransportStatement`, from go-lemma42.

Notes for the producers:
- If `MultipleEdgePocketRegionInput` moves to an O-equivalent copy (ROSTER ruling B), the core
  lemma already covers it. The restated Input must also give label legality on the copy,
  `∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)`, and `Nonempty (OEquivalentDiscDiagram
  Δ X)`, so the assembly only changes its final `exact`.
- The side-length bounds `s₁.length ≤ ε`, `s₂.length ≤ ε` of `MultipleEdgePocketRegionInput`
  are unused: the collar words have length `wordNorm ≤ ε`. The Input can drop them.

## Holds and next

- Hold: no edits to `OsinPocketZeroCellMerge.lean` or `OsinPocketZeroCellMergeFalse.lean` until
  ghw-charp2's LoopCut census patches 01-09 land (ruling A). The loop-ruling version of the False
  module is at `$NM/backup/hull-select/loopcensus-OsinPocketZeroCellMergeFalse.lean.patched`.
- `pocketOuterTransport` closes the `houter` binder of the section pocket cut assembly
  (`OsinPocketPieces`). The cell transport `hcell` is still go-lemma42's.
- Next: item 2, the O-equivalent-copy restatement of `MultipleEdgePocketRegionInput`. It waits
  for dgo-analytic's R2/R1 carrier fix (ROSTER line 743). The draft is at
  `$NM/drafts/hull-select-copy-input.lean`. Under R2 the inner `FollowsBoundary` leaves the
  Input, but `nonempty_osinMultipleEdgeCut_of_pocketRegion` still passes `hin` to
  `exists_twoCollars_of_ne_or` and `GeodesicCollarStatement`. So R2 also needs kh-torsion's
  collar restated without it.
- The assembly modules are infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7)
  and certify no printed sentence on their own, so there are no census rows.
