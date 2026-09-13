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
