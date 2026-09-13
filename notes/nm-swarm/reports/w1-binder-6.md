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
| `cell_self`, `regions` | copies (b)/(c), ruled to leavitt-units at 14:00; nothing in flight |

## Progress log
- 17:0x: claim landed (c0892aaee).
- 17:3x: module written, attic copy e854e80fa, probe 1 started.
- 17:4x: probe 0913-173850-9813 GREEN (BUILT; md5 matches the green record). LANDED 538fe1b33, on origin. Queued for
  wiring: `GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening w1-binder-6 538fe1b33`.
- Next: generic transport lemmas across a region correspondence that keeps target profiles and source indices
  (exterior membership, `TargetsSectionIndex`, distinctness), so a consumer can move `a ≠ b` to the copy. Then
  `side_outer`.
