# Lane w1-binder-6: second start on `OsinSectionPocketFaceSetSectionStatement`

Lead: session `nonsofic-existence-49` (wave 2, `notes/nm-swarm/reports/ct-lead.md`). The owners of record are kh-ejz,
cite-hull, hl-lemma46, sec2-sentences, hull-select and hull-euler. This lane never edits their files and lands only
new modules.

## State on origin (19d96c2c5, 16:41)

- kh-ejz's `PocketWalk.exists_pocketFaceSet_of_exteriorAt_of_value` (Estimating/OsinPocketWalkFaceSet, 336b8afeb)
  turns two distinct exterior regions of one cell to one section into a pocket face set in walk order. It needs
  least area, `K.CopyClean x y` (Estimating/OsinPocketCopyWalk), no relator of value one, and that the outer cycle
  of the noncrossing walk follows its boundary.
- The module docstring says what is still missing: an O-equivalent copy with legal labels that satisfies the edge
  conditions `CopyClean`.
- `CopyClean` has six conditions. hs-vanishes' `outerSpurThickening` (36ff632cd) gives `spur` on a copy. The copies
  for the other five were ruled to leavitt-units at 14:00. No producer is on origin, in the shared tree, in any
  `lanes/*.files` or in the lane backups (checked 17:0x).

## CLAIM

- `CLAIM outer cell-edge thickening GroupApproximation/GGT/VanKampen/SurgeryOuterCellThickening.lean`
  - A distinguished section family has a distinguished section family over the same cuts, on an O-equivalent
    diagram, with no outer spur and no edge between a relator cell and the exterior. The regions correspond with the
    same weight, target profiles and source indices.
  - This gives `CopyClean.cell_outer` for every source cell.
  - Route: the outer-dart doubling of `SurgeryOuterSpurThickening`, applied to outer darts whose reverse lies on a
    relator cell. Regions never contain a relator cell, so the region family avoids the doubling. Induct on the
    number of outer cell darts.

## Module `GGT/VanKampen/SurgeryOuterCellThickening.lean` (probe 0913-173850-9813 GREEN, BUILT; unwired)

Namespace `GroupApproximation.GGT.VanKampen.OuterCellThickening`. It imports only `SurgeryOuterSpurThickening` and
`AxiomGuard`. These names are stable, so consume them:

| declaration | content |
|---|---|
| `IsOuterCellDart Delta x` | `faceOf x = outerFace ∧ ∃ C ∈ relatorCells, C.face = faceOf (alpha x)` |
| `OuterCellThickeningStatement`, `outerCellThickening` (closed) | for `S` over `Delta` with `1 < Delta.boundaryWord.length` and no relator word of value one: `∃ S' e`, O-equivalent, no outer spur, no outer cell dart, no relator word of value one, same weight, same target profiles and source indices |
| `spur_of_noOuterSpur` | `CopyClean.spur` |
| `cell_outer_of_noOuterCellDart hno i` | `CopyClean.cell_outer` for the source cell `i` |
| `leastArea_of_oEquivalent`, `relatorValue_ne_one_of_oEquivalent` | least area and the value condition pass to O-equivalent diagrams |
| `sectionFamilyOfAvoid S j hlen havoid` | the spur thickening's `sectionFamily`, with any `havoid` in place of the spur hypothesis |
| `exists_of_isOuterCellDart`, `outerCellCount_lt`, `noOuterSpur`, `cell_avoid`, `exists_cellFree` | the induction |

Route: double the exterior along an outer cell dart. The new exterior dart has its reverse on the digon, and the
digon is no relator cell, so the number of outer cell darts drops by one. `exists_of_isOuterSpur` holds for any outer
doubling, so no spur appears. When no relator word has value one, no region contains a relator cell, so every region
avoids the face across the doubled dart. `outerCellThickening` runs `outerSpurThickening` first and then this
induction.

## Split of `CopyClean` (agreed with ms-cite-2, 17:3x)

| field | owner |
|---|---|
| `spur` | hs-vanishes `outerSpurThickening`, carried along by this module |
| `cell_outer` | this lane (above) |
| `side_cell` | ms-cite-2: `SurgeryCellSideThickening`, plus a side-dart variant of the doubling transport (`SurgeryFaceEdgeDoublingSideRegions`) |
| `side_outer` | this lane, after ms-cite-2's variant transport interface lands |
| `cell_self` | ms-binary (`SurgeryCellSelfEdgeThickening`, induction on relator self-edges via `FaceEdgeDoublingRegions.regionFamily`; model test against least area first) |
| `regions` | ms-intro-2 (`SurgeryRegionPairThickening`, over ms-cite-2's side-dart transport bb3a56f4e; ms-binary withdrew its offer) |
| `side_outer` | this lane: `outerSideThickening`, LANDED acd63f3bb |

## Module `GGT/VanKampen/Estimating/RegionProfileTransport.lean` (probe 0913-175337-49759 GREEN; LANDED 8755e832c; wire-queued)

Namespace `...VanKampen.RegionProfileTransport`. The correspondence is `e : selected ≃ selected'` with
`he : ∀ a, SameTargetProfile (e a).1 a.1 ∧ (e a).1.2.source.val = a.1.2.source.val`, which is the output shape of
every thickening above.

| declaration | content |
|---|---|
| `mem_exteriorAt e he hi a ha` | exterior region of cell `i` ↦ exterior region of cell `i'` whenever `i'.val = i.val` |
| `targetsSectionIndex hab hb` | `TargetsSectionIndex cuts j` passes along a same target profile |
| `val_ne e hab` | distinct regions stay distinct |
| `exists_exteriorPair e he ha hb hab hja hjb` | the pair `a ≠ b` of `exists_pocketFaceSet_of_exteriorAt_of_value`, on the copy |

## Module `GGT/VanKampen/SurgeryOuterDoublingTransport.lean` (probe 0913-180428-94428 GREEN; LANDED 3374bf4ed; wire-queued)

Namespace `...VanKampen.OuterDoublingTransport`. The spur module's transport, with `alpha w_j ∉ H.targetArc.darts` in place of
`faceOf (alpha w_j) ∉ s`: `contiguityGeometry H htgt`, `Transportable`, `regionCandidate`, `regionCandidate_sides` (the sides are the
images under `embed`), `mem_regionFamily`, `regionFamily`, `_profile`, `_noLoop`, `_card`, `_weight`, `_pairwise`,
`regionFamilyEquiv`, `_profile`, `_source`. Producers: `not_mem_targetArc_of_avoid` (old hypothesis) and
`alpha_dart_not_mem_targetArc_of_side` (side dart of its own region).

## Module `GGT/VanKampen/SurgeryOuterSideThickening.lean` (probe 0913-181351-32575 GREEN; LANDED acd63f3bb; wire-queued)

Probe 0913-180632-902 FAILED on `Option.noConfusion hex` (implicit universe) in the digon case of
`exists_of_isOuterSideDart`; the four `sorryAx` audit errors only propagated from it. The fix is
`(Option.some_ne_none _ hex).elim` (attic 28b2567e0).

Composition agreed outer-first:
1. `outerSideThickening`
2. ms-cite-2 `cellSideThickening` (dc394dd8e) through `exists_cellSideFree_of_invariant`, plus its preserving module
3. ms-binary `cell_self`
4. ms-intro-2 `regions` (`SurgeryRegionPairThickening`)

Each later step takes and returns the outer invariants.

Namespace `...VanKampen.OuterSideThickening`:
- `IsOuterSideDart Delta family x` holds when `faceOf x` is the exterior and `alpha x ∈ a.2.rightSide ++ a.2.leftSide` for some
  `a ∈ family`.
- `side_outer_of_noOuterSideDart` gives `CopyClean.side_outer`.
- Closed `outerSideThickening : OuterSideThickeningStatement` has the `OuterCellThickeningStatement` output plus no outer side dart.

## CLAIM (18:3x, main's item): the pocket-level assembly of binder 6 on the copy

`CLAIM binder-6 pocket assembly GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFaceSetOnCopy.lean`. Ownership check: no
in-flight draft in `kh-ejz.files`, in the shared tree, or among unlanded users of `SectionPocketFaceSetInput`.

LANDED fe02830d0 (probe 0913-183359-68514 GREEN, md5 checked; wire-queued). The two remaining residuals of binder 6 are
`SectionPocketRegionsCopyStatement` (ms-intro-2's `regions` stage) and `SectionPocketKeptCellStatement` (the kept
relator cell; no owner yet).

Design:
- `PocketFaceSetOnCopy.exists_copyClean` composes the four stages:
  1. `outerSideThickening` (acd63f3bb)
  2. `cellSideThickeningPreserving` (ms-cite-2, c3bd2ee44)
  3. `cellHairSidesThickening` (ms-binary, a36060868)
  4. named residual `SectionPocketRegionsCopyStatement` (ms-intro-2's stage, in the global `CopyClean.regions` form)

  It then builds all six `CopyClean` fields for every pair of distinct exterior regions of one cell.
- Named residual `SectionPocketKeptCellStatement`: on a least-area copy, the pocket walk of two distinct exterior regions
  of one cell to one section, satisfying `CopyClean`, has a relator cell on its side. This is Osin's "a pocket without an
  R-cell merges the two regions".
  - It replaces `hfollows`: sec2-sentences' lake (Configuration B, sides touching at a vertex) breaks `hfollows` and
    `FirstTurn` for `K.walk`, and `CopyClean` forbids shared edges, not vertex touches.
  - `hfollows` implies the kept cell (`exists_kept_of_noncrossing_of_value`), so the residual is weaker.
- `sectionPocketFaceSetInput_of_residuals` goes through `RegionProfileTransport.exists_exteriorPair` and kh-ejz's first
  variant `exists_pocketFaceSet_of_exteriorAt`.
  - `one_lt_boundaryWord_length` gets the length hypothesis from two distinct regions to the boundary.
  - `osinSectionPocketFaceSetSection_of_residuals` then gives waist residual 5 with `eps0 = 0`, `rho0 = 1`.

## CLAIM (19:0x, main's item): binder 6 residual 2, `SectionPocketKeptCellStatement`

`CLAIM kept cell of the section pocket walk GroupApproximation/GGT/VanKampen/Estimating/OsinPocketKeptCellSection.lean`.
Ownership check: no in-flight drafts on non-interleaving walks or on Euler without following.

The problem:
- Kind (i) joints (inside a side, and the four corners): the inner sector holds only darts internal to the region,
  so the inner cycle follows there. A touch there breaks only the outer cycle, which is the lake.
- Kind (ii) joints (inside `t_1`, `t_2`): the outer sector is one corner, but the inner sector is uncontrolled. A
  touch there breaks the inner cycle.
- A walk with touches of both kinds breaks both cycles, so "either cycle follows" is not the residual (hand argument).

What a pocket region actually needs:
- `IsDiscRegion` is a boundary cycle plus the Euler equality of its reclosing; connectivity comes free
  (`toDiscRegion_of_euler`).
- So option (iv) is the precise residual: both reclosings of the pocket walk preserve the Euler characteristic.
- Passages at a vertex do not interleave, so both sides are discs (hand argument).

LANDED 2c1a841e8 (probe 0913-191427-58413 GREEN, md5 checked; wire-queued). Module `Estimating/OsinPocketKeptCellSection`:
- `IsNoncrossingClosedWalk.eulers_of_eitherFollows`: one following cycle gives both Euler equalities.
- `PocketRegion.ofNoncrossingClosedWalkEuler` (with `_faces` and `_inner_cycle`, both `rfl`): the pocket region from the two
  Euler equalities.
- `PocketWalk.noncrossing_of_copyClean`: the pocket walk under the edge conditions is noncrossing.
- `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingPocketWalk_of_eulers`.
- Named residual `SectionPocketWalkEulerStatement` (option (iv)); `sectionPocketKeptCell_of_euler`;
  `osinSectionPocketFaceSetSection_of_regions_euler`.
- Model `OsinPocketKeptCellSection.lakeEulerBranch` (closed): on the lake map the outer cycle does not follow, and both
  Euler equalities hold.

Binder 6 residuals after this module: `SectionPocketRegionsCopyStatement` (ms-intro-2) and
`SectionPocketWalkEulerStatement` (no owner).

## `SectionPocketProperGapStatement` (main's item, 19:1x): BLOCKED, not refuted

- Checked: `toPocketFaceSetOfNoncrossing` keeps the source arc (`PocketFaceSet.ofBoundaryCycle` sets
  `sourceArc := sourceArc`, so `rfl`).
- The route through `OsinCCondition` does not apply.
  - The condition bounds published pieces between relator words, measured in `G`, where relator words have value ≠ 1.
  - The pocket contains a relator cell, so its boundary value in `G` is a product of relator conjugates. So `t_1` is
    not ε-close to `t_2` in `G`.
- The enclosed lake breaks the bound.
  - Take `y`'s source arc ending where `x`'s begins, at a vertex `v` of `∂Π`. Then `x.arc ++ Gap ++ y.arc = ∂Π`, the
    sides `s_1` and `s_2` meet at `v`, and `Π` borders the pocket along all its edges and touches the outside only at
    `v`.
  - This is Configuration B with `Π` alone in the lake. In `OsinPocketLakeModel`, `t_1 = [0]` is all of `∂Π`.
  - The edge conditions do not exclude vertex touches.
- The only exclusion I see is global.
  - Gluing `Π` into the pocket gives a subdiagram with boundary `s_1 s_2 t_2` that contains a relator of length ≥ ρ.
  - Ruling that out is Greendlinger / Lemma 9.7 for that subdiagram, which need not have fewer cells than `Δ`.
- Suggested: handle a full `t_1` at the pinch step. `OsinPocketArcTrim` trims when a side is shorter than ε, and the
  stuck case is both sides at exactly ε.

## Full-`t_1` exclusion through `OsinLemma97Below` (main's item, 19:3x): FAILS the model test, nothing landed

Binder: `OsinLemma97Below … n := ∀ Xi cutsXi, Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < n →
∃ T, OsinLemma97bConclusion mu T`, where the conclusion is one cell with total contiguity to the sections > 1 − 13μ.

1. **Counting.**
   - D₁ = Γ₁ ∪ Π has fewer relator cells than Δ only if some relator cell lies outside Γ₁ ∪ Π.
   - Configuration: the full-`t_1` lake, with every relator cell of Δ in the V bounded by `s_1`, `s_2` and `t_2`, and
     only G-faces outside.
   - Then `D₁.rCellCount = Δ.rCellCount`, and the binder does not apply.
2. **No contradiction even with fewer cells.**
   - 9.7(b) for D₁, with sections `s_1 s_2` (≤ 2ε) and `t_2`, holds through a cell running along the long
     quasi-geodesic arc `t_2`.
   - The short sides bound only the contiguity to themselves.
3. **Diagnosis.**
   - A full `t_1` is a genuine case in Osin. Γ₁ is a singular disc with four sections, passing `v` twice, and it has
     fewer cells.
   - The formal obstruction is the simple carrier (`PocketFaceSet.not_simple_of_full_sourceArc`).
   - Options put to main: (a) a singular `DiscDiagram` carrier for the section pocket cut; (b) a separate full-`t_1`
     piece of `SectionPocketCutInput`.

## CLAIM (20:2x, main's ruling (a)): the singular Γ₁ carrier for a full `t_1`

- Recorded: **a full `t_1` is a genuine case of Osin's proof.** Γ₁ is a singular disc with four sections through the
  touch vertex, and it has fewer cells. `SectionPocketFullArcExcludedStatement` is dropped for good.
- `CLAIM lake model GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFullArcLakeModel.lean` and
  `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFullArcLakeEnclosed.lean` (Ξ realized), to be landed first.
- ~~`CLAIM singular carrier GroupApproximation/GGT/VanKampen/Estimating/OsinPocketEnclosedCarrier.lean`~~ superseded
  (23:5x): the successor route does not cover a full `t_1` (below), so the carrier goes through the Euler pocket region.
  The path is released and nothing was written there.
- **LANDED bda10ebe8** `Estimating/OsinPocketFullArcLakeModel` (probe 0913-234651-11200 GREEN, md5 checked; wire-queued).
  Closed `fullArcLake : FullArcLakeStatement`. `OsinPocketFullArcLakeEnclosed` was never written; `lakePocket` realizes
  Ξ instead.
- Open, ruling asked of main (00:0x): transports over a non-following outer cycle. `PocketCellTransportStatement` and
  `PocketOuterTransportStatement` assume `P.outer.FollowsBoundary` for `PocketRegion.glueDiagram`.
  - Scope of option (i): `glueDiagram` uses following only for `Seam.glueMap_planar` (`SurgeryPocketGluePlanar`). That
    lemma needs it in three places:
    - the reclosed piece is planar (`reclosedMap_planar`). The complement's Euler equality replaces this, since
      `toDiscRegion_of_euler` gives connected plus χ.
    - `glueMap_connected`, through `eqvGen_glueEmbedding` / `glue_sigma_firstReturn`.
    - `glue_vertexCount` (`SurgeryPocketGlueVertices`).
  - So option (i) means generalizing the glued map's vertex rotation, connectivity and vertex count from a following
    cycle to a disc complement given by Euler. Model-test first: glue `lakePocket.diagram` back into the lake along
    `[3,1]`.
  - ms-traces-2's `enclosedFaceSetSuccOfNoncrossing` assumes `hfollows` too, so it does not reach a full `t_1`
    (bda10ebe8 `not_enclosedFaceSetSucc`).

## CLAIM (00:1x, main): (i) the pocket transports over a non-following Euler pocket region

main accepted the pivot: Γ₁ is `(ofNoncrossingClosedWalkEuler …).diagram`, then `fourSectionCuts_leastAreaCut`, with no
enclosed Prop. This lane owns (i). The work is additive; no owner's file is edited.
- `CLAIM glue planarity from Euler GroupApproximation/GGT/VanKampen/SurgeryPocketGlueEuler.lean`: `Seam.glueMap_planar`
  and connectivity, with the complement's Euler equality in place of `S.boundary.FollowsBoundary`, plus the vertex
  count.
- `CLAIM transports GroupApproximation/GGT/VanKampen/Estimating/OsinPocketGlueTransportEuler.lean`: the variants of
  `PocketCellTransportStatement` and `PocketOuterTransportStatement` without `P.outer.FollowsBoundary`, and their
  proofs.
- `CLAIM glue model GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFullArcLakeGlueModel.lean`, landed first:
  `lakePocket.diagram` glued back into the lake along `[3,1]`.

Design:
- Γ₁ is the enclosed subdiagram Ξ of the pocket walk. Its faces are `sideFaces X K.walk`, with outside walk
  `invDarts X K.walk`, through ms-traces-2's `ClosedWalkEnclosedSubdiagramStatement` (named) and
  `enclosedSubdiagram_leastAreaCut`.
  - Ξ reads `s_1 t_1⁻¹ s_2 t_2`. The source cell is off the side and the kept cell on it, so
    `0 < Ξ.rCellCount < X.rCellCount` and Ξ is least area.
  - Four sections by `SectionCuts.ofParts`.
- The enclosed face set needs no following cycle. Chain, closes and `mem_iff` go as in ms-intro-1's draft
  `ClosedWalkEnclosedNoncrossing`. `turn_mem` is the turning field of `IsNoncrossingClosedWalk.reverseMapAlpha`.
  - `EnclosedFaceSetOfNoncrossingStatement` assumes the complement cycle follows. That fails on the lake
    (`OsinPocketLakeModel.lakeCycle_outerCycle_not_followsBoundary`), which is exactly the full-`t_1` configuration.
- Lake model (Configuration B, Π alone in the lake):
  - Δ is the rose with `K = [0,2]`, `Π = [1]` and `O = [3]` over `Perm (Fin 3)`, with `W = {[a], [a⁻¹, c]}` (`a` a
    transposition, `c` a 3-cycle). It is least area by sign parity.
  - The pocket walk is `[0,2]`, with `t_1 = ∂Π` full, `t_2 = [2]` and empty sides. Π and O are off the side, and the
    enclosed face set holds while the outer cycle does not follow.
  - Ξ is realized as the one-cell bigon reading `[a⁻¹, c]`: least area, 1 < 2 cells.

| piece | owner |
|---|---|
| `ClosedWalkEnclosedSubdiagramStatement` | ms-traces-2's Prop; producer unowned; consumed by name |
| `EnclosedLeastAreaFilterStatement` | ms-traces-2, with ms-inverses-1 |
| unconditional enclosed face set of a noncrossing walk | proposed to ms-intro-1 |
| carrier and lake model | this lane |

### Successor-form route (main, 21:22 / 23:12): does not cover the full `t_1`; pivot to the Euler pocket region

- At the lake, rotating from `α 3 = 2` the first dart on a walk edge is `σ 2 = 3` itself.
  - Every outside walk of the side holds `3` and `1`. A duplicate-free list of length ≥ 2 never has `3` as the successor
    of `3`.
  - So `EnclosedFaceSetSucc diagram (sideFaces lakeWalk) outerWalk` fails for every `outerWalk`
    (`OsinPocketFullArcLakeModel.not_enclosedFaceSetSucc`).
  - `turn_next` for the reversed pocket walk is the outer cycle following its boundary, which is what the lake breaks.
    So `ClosedWalkEnclosedSubdiagramSuccStatement` never applies to a full `t_1` in a lake.
  - The plain `EnclosedFaceSet` does hold there, but its least-area filter is refuted (ms-inverses-1).
- The case is still carried, without the enclosed route. On the copy the pocket walk has no bridge (`CopyClean`), so it
  is noncrossing.
  - From both Euler equalities, `PocketRegion.ofNoncrossingClosedWalkEuler` (2c1a841e8) gives a pocket region.
  - `PocketRegion.fourSectionCuts_leastAreaCut` then gives the least-area four-section cut with `0 < cells < Δ.cells`.
  - At the lake: `lakePocket_leastArea`, `lakePocket_rCellCount_pos`, `lakePocket_rCellCount_lt` (1 of 2 cells) and
    `lakePocket_decomposition`.
  - The Euler equalities for the section walk are ms-inverses-2's (`SectionPocketWalkNoninterleavingStatement` plus
    `NoninterleavingVertexCountStatement`).
- What remains for `OsinSectionPocketCut`: the two transports. `PocketCellTransportStatement` and
  `PocketOuterTransportStatement` assume `P.outer.FollowsBoundary`, which a full `t_1` breaks. The carrier needs
  variants over the Euler pocket region.

## Plan for `side_outer`

- Mirror ms-cite-2's cell-side statement for the exterior: `IsOuterSideDart Delta family x` holds when `faceOf x` is
  the exterior and `alpha x ∈ a.2.rightSide ++ a.2.leftSide` for some region `a`.
- The spur module's transport uses `faceOf (alpha w_j) ∉ s` only to get `alpha w_j ∉ targetArc.darts`. The owning
  region gets that instead from `alpha w_j` being a side dart and the boundary cycle having no repeated dart. Every
  other region avoids the face, since regions are disjoint.
- Induction on the number of outer side darts. The statement keeps no outer spur, no outer cell dart and no relator
  word of value one.

## Progress log
- 17:0x: claim landed (c0892aaee).
- 17:3x: module written, attic copy e854e80fa, probe 1 started.
- 17:4x: probe 0913-173850-9813 GREEN (BUILT; md5 matches the green record). LANDED 538fe1b33, on origin. Queued for
  wiring: `GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening w1-binder-6 538fe1b33`.
- Next: generic transport lemmas across a region correspondence that keeps target profiles and source indices
  (exterior membership, `TargetsSectionIndex`, distinctness), so a consumer can move `a ≠ b` to the copy. Then
  `side_outer`.
