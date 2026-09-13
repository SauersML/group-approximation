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
- 3f87827d0, `GGT/VanKampen/Estimating/OsinPocketMultipleEdgeCut.lean`. The module is
  unwired. It was probed green in 0913-025730-78976 (base 517188c31) and uses only the
  classical axioms.
  - `OsinMultipleEdgeCut.ofRegionCut`: builds an `OsinMultipleEdgeCut D λ c ε Δ` for a
    least-area `Δ`, taking:
    - `equiv : OEquivalentDiscDiagram Δ Δ'` (for example `S.equiv`, `Δ' = S.diagram`);
    - a `RegionCutData Δ'` with `0 < cells.length`;
    - the partition `invDarts Δ' cycle = s₁ ++ t₁ ++ s₂ ++ t₂` with quasi-geodesic parts;
    - `|s₁|, |s₂| ≤ ε`;
    - the transport for sections 1 and 3, into O-equivalent copies of `Δ'`.
  - Least area and the relator count move along `equiv`, and the transport composes
    with `OEquivalentDiscDiagram.trans`.

## Residual Props for `MultipleEdgeCutInput`

1. (a), owner dgo-analytic. From two distinct regions `a ≠ b` of a globally distinguished
   family joining cells `i`, `j` of `S.diagram`, it must give a pocket carrier.
   - The carrier has boundary walk `s₁ t₁ s₂ t₂`: `s₁`, `s₂` are sides of `a`, `b`, and
     `t₁`, `t₂` are arcs of the two cells.
   - It keeps at least one relator cell. The zero-cell pocket is excluded by merging.
   - Open question, sent to the lead 09-13: is the carrier a full `RegionCutData` or only
     the outside face set with `IsDiscRegion`?
     - Full `RegionCutData`: `cells_infix` is against `Δ'`'s own ordered cells, and
       `shelling` is indexed by the kept block's conjugators `basepoint⁻¹ * C.conjugator`
       (`SurgeryCutRecord.lean:52`).
     - `DiscDiagram.boundary_product` ties that order to the van Kampen product, so the
       cells can't just be permuted. A producer has to pass to an O-equivalent copy `Δ''`
       (same map) whose cell list holds the pocket's cells as a block with conjugators
       taken from a shelling of the pocket. The cells before and after must be rebased so
       that the product still reads the outer word.
     - Main has no such rebasing construction. `ofRegionCut` accepts any O-equivalent
       `Δ'`, so it takes `Δ''` directly.
     - Outside face set only: the piece comes from `DiscDiagram.ofPlanar`
       (`VanKampen/PlanarVanKampenDiagram.lean:156`, closed) without infix or shelling.
       Its least area then needs a weighted planar van Kampen on `Δ` with the inside
       collapsed, so (a) would also have to give `IsDiscRegion` for the inside face set.
   - Open question, sent to the lead 09-13: `MultipleEdgeCutInput` allows `i = j`, which
     is two distinct loops at the same cell.
     - Proposal: add an `i ≠ j` binder. Both consumers already prove NoLoops, and at
       `i = j` the `hloop` branch gives False.
     - That means about 4 lines in `OsinAppendixDescentInduction.lean` (dgo-analytic's
       files) and in `OsinAppendixSectionInduction.lean` (hull-select).
     - Otherwise (a) must also cover a pocket whose two cell arcs lie on one cell.
2. (c), owner go-lemma42: the transport for sections 1 and 3, as `ofRegionCut` takes it.
   - For every O-equivalent copy `Xi` of the piece, and every region of `Xi` to section 1
     or 3,
   - there is a region of an O-equivalent copy of `Δ'` from another cell to a relator
     cell, with the same contiguity degree.

## Next

- After (a) and (c) land: the closed `MultipleEdgeCutInput` producer is `ofRegionCut`
  applied to `S.equiv`, the carrier of (a), and the transport of (c).
- After the lead rules on `i ≠ j`: restate `MultipleEdgeCutInput` and probe it together
  with its users (`OsinAppendixAssembly`, `OsinAppendixLemma97Pocket`,
  `OsinAppendixGreendlingerParts`, `OsinAppendixDescentInduction`).
