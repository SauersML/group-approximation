# hull-select report

Lane `hull-select` of the non-MF every-line swarm (09-13).

## Target

- Roster target: a closed `MultipleEdgeCutInput`
  (`GGT/VanKampen/Estimating/OsinAppendixSectionInduction.lean:75`), stated uniformly in
  the parameters as `OsinMultipleEdgeCutSectionStatement`
  (`Estimating/OsinAppendixGreendlingerParts.lean:49`).
- Reassignment 09-13 ~02:00 (W1 pocket cut core, owned by dgo-analytic): this lane takes
  piece (b), the least-area cut with four sections.

## Landed

- aa1b561db, `GGT/VanKampen/Estimating/OsinPocketLeastAreaCut.lean`. The module is unwired.
  It was probed green in 0913-022934-79111 (base aa1b561db), and the landed bytes are the
  probed bytes. It uses only the classical axioms.
  - `RegionCutData.diagram_boundaryWord`: the piece reads
    `dartWord Δ (invDarts Δ region.cycle)`.
  - `RegionCutData.boundarySectionCuts`, `_count`, `_part`, `_cut_sub`: an exact partition
    of the inverted cycle into 1 to 4 ambient parts with `(λ, c)`-quasi-geodesic words
    gives `SectionCuts D λ c cut.diagram.boundaryWord`, whose sections are the part words.
  - `RegionCutData.fourSectionCuts s₁ t₁ s₂ t₂`, `_count` (= 4), `_side_short`
    (`|s₁|, |s₂| ≤ ε` gives sections 0 and 2 at most `ε`).
  - `RegionCutData.fourSectionCuts_leastAreaCut`: from `Δ.LeastArea` and `0 < cells.length`,
    the piece is least area, `0 < rCellCount < Δ.rCellCount`, `count = 4` and the sides are
    short. These are the first seven fields of `OsinMultipleEdgeCut` (hull-select) and of
    `OsinExteriorDoubleCut` (dgo-analytic), with `enclosed := cut.diagram`.

## Residual Props for `MultipleEdgeCutInput`

1. (a), owner dgo-analytic. From two distinct regions `a ≠ b` of a globally distinguished
   family joining cells `i`, `j` of `S.diagram`, it must give a pocket carrier.
   - The carrier has boundary walk `s₁ t₁ s₂ t₂`: `s₁`, `s₂` are sides of `a`, `b`, and
     `t₁`, `t₂` are arcs of the two cells.
   - It keeps at least one relator cell. The zero-cell pocket is excluded by merging.
   - Open question, sent to the lead 09-13: is the carrier a full `RegionCutData`
     (`cells_infix` plus `CellShelling`, which needs hull-respell's shelling producer and a
     re-ordering of `Δ`'s cells), or only the outside face set with `IsDiscRegion`?
     - In the second case, the piece comes from `DiscDiagram.ofPlanar`
       (`VanKampen/PlanarVanKampenDiagram.lean:156`, closed) without infix or shelling.
     - Its least area then needs a weighted planar van Kampen on `Δ` with the inside
       collapsed, so (a) would also have to give `IsDiscRegion` for the inside face set.
2. (c), owner go-lemma42: the `transport` field for sections 1 and 3.
3. Assembly (hull-select, once (a) and (c) are stated): `OsinMultipleEdgeCut` from
   `fourSectionCuts_leastAreaCut`, the transport, and `S.equiv` (count and least area
   through `OEquivalentDiscDiagram.leastArea`).

## Next

- Build the (b) Prop that matches the carrier dgo-analytic fixes for (a).
- Build the `OsinMultipleEdgeCut` assembly once the (a) and (c) Props land.
