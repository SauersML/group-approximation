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

## Progress log
- 17:0x: claim landed; the statement module comes next.
