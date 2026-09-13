# hull-select report

Lane `hull-select` of the non-MF every-line swarm (09-13).

## Target

- Roster target: a closed `MultipleEdgeCutInput`
  (`GGT/VanKampen/Estimating/OsinAppendixSectionInduction.lean:76`), stated uniformly in
  the parameters as `OsinMultipleEdgeCutSectionStatement`
  (`Estimating/OsinAppendixGreendlingerParts.lean:49`).
- Current piece, after the lead's 04:05 reconciliation: (b), which rebases the section layer
  on dgo-analytic's `PocketRegion` (`Estimating/OsinPocketRegion.lean`, 497542415) with no
  separate structure. (a) is assembled by dgo-analytic in `OsinPocketPieces`; (c) belongs to
  go-lemma42.

## Landed

- aa1b561db, `Estimating/OsinPocketLeastAreaCut.lean`: section layer on `RegionCutData`
  (`diagram_boundaryWord`, `boundarySectionCuts`, `fourSectionCuts`, `_side_short`,
  `_leastAreaCut`). It is closed but unused: RegionCutData has no producer, because its
  shelling went through the refuted `FaceSetEarStatement`.
- 3f87827d0, `Estimating/OsinPocketMultipleEdgeCut.lean`: `OsinMultipleEdgeCut.ofRegionCut`.
  It is closed and unused for the same reason.
- 45e7201da, `Estimating/OsinPocketRegionSections.lean`, on top of `PocketRegion`. The module
  is unwired. It was probed green in 0913-042552-816 (base 57071835a, BUILT) and uses only
  the classical axioms (`#audit_axioms` in the file).
  - `PocketRegion.boundarySectionCuts` (+ `_count`, `_part`, `_cut_sub`): an exact partition
    `invDarts Δ P.outer.cycle = parts.flatten` into 1 to 4 parts with `(λ, c)`-quasi-geodesic
    words gives `SectionCuts D λ c P.diagram.boundaryWord`, whose sections are the part
    words in order.
  - `PocketRegion.fourSectionCuts s₁ t₁ s₂ t₂` (+ `_count` = 4, `_side_short`).
  - `PocketRegion.fourSectionCuts_leastAreaCut`: from `Δ.LeastArea`, one relator cell with
    face in `P.faces` and one with face outside, the pocket is least area, has
    `0 < rCellCount < Δ.rCellCount`, has four sections, and has short sides.
  - `OsinMultipleEdgeCut.ofPocketRegion`: the ofPlanar analogue of `ofRegionCut`. It takes
    `equiv : OEquivalentDiscDiagram Δ Δ'`, `hlea`, `P : PocketRegion Δ'`, the two cells, the
    partition, `hquasi`, `|s₁|, |s₂| ≤ ε`, and the transport for sections 1 and 3.
- b45e7ef30: the `i ≠ j →` binder on `MultipleEdgeCutInput`, approved by the lead, in one
  landing across `OsinAppendixSectionInduction.lean` and `OsinAppendixDescentInduction.lean`.
  - Both consumers (`osinLemma97_atParameters_of_inputs`, `exists_elevenCell_of_below`) split
    on `i = j` and handle the loop case through `LoopCutInput`.
  - It was probed green in 0913-042552-816 together with the other users: OsinAppendixAssembly,
    OsinAppendixLemma97Pocket and OsinAppendixGreendlingerParts.

## Residual for `MultipleEdgeCutInput`

The producer is `OsinMultipleEdgeCut.ofPocketRegion` at `equiv := S.equiv`, `Δ' := S.diagram`.
It still needs:
1. (a), assembled by dgo-analytic in `OsinPocketPieces`, from `a ≠ b` joining `i ≠ j`:
   - a `PocketRegion S.diagram`: kh-ejz supplies the region-side data, hull-respell the pinched
     pocket, and kh-torsion the collar insertion;
   - a relator cell inside and one outside;
   - the partition `s₁ t₁ s₂ t₂` with quasi-geodesic parts and short sides.
   Under the collar ruling, `hquasi` holds on sides only after a G-face collar with geodesic
   labels, because spur sides are not quasi-geodesic when `c = 0`.
2. (c), owned by go-lemma42: the transport for sections 1 and 3 against `PocketRegion.diagram`.
