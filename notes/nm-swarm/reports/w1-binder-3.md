# w1-binder-3: second start on `OsinLemma94CaseOneSameCellStatement` (2026-09-13)

Lane of session nonsofic-existence-49 (wave 2 of the every-sentence swarm). It owns no file of
another lane and consumes their names only.

## Binder map (origin/main 19d96c2c5, shared tree read at 16:56)

- Statement: `Estimating/OsinUnboundCaseOneFace.lean:476`, with the `OsinLemma97Below` binder since
  48c6cc71e. The leaf census (`drafts/w1-leaves-0913.md` l.302) records it as true and not cheaply
  vacuous.
- Cell-free branch: ko-closed's `false_of_sameCell_cellFree_pocketRegion_X` and `_Y` (29c1eeae3,
  green, unwired).
- Producer: jacobson (roster l.919). Its in-flight module `Estimating/OsinLemma94OneCellSameCell.lean`
  (listed in jacobson's files, edited 16:49) has the value-one kills `false_of_sameCell_value_one_X`
  and `_Y`. Its docstring plans `OsinLemma94CaseOneRCellStatement`, `OsinLemma94CaseOnePocketStatement`
  and `osinLemma94CaseOneRCell_of_pocket`. This lane does not rebuild any of them.
- Arcs `A` and `T`: the in-flight `Estimating/OsinLemma94SameCellSpan.lean` (16:42) supplies them.
  Not rebuilt here.
- Relator-cell branch: `nonempty_osinLoopCut_of_pocketRegion` (70f8cd913) plus
  `OsinLoopCut.false_of_below`. Its binders are `GeodesicCollarStatement` (binder 8) and
  `PocketCellTransportStatement`, and ruling R1 keeps `hin`.
- Walks that are not simple: hair opening (kh-cckw) and bubble un-pinch (leavitt-units), both
  stated by sec5-sentences (rulings 16:00–16:17).

## The sub-leaf taken here

Some rotation of the face walk reads `X q⁻¹ Y p⁻¹`, and some rotation of `∂Π` reads `q B p A`.
So `X B` and `Y A` are closed walks, and the pocket walks are `invDarts X ++ invDarts B` and
`invDarts Y ++ invDarts A`. When neither reads `1`, the producer takes the side of one of them that
avoids the exterior face. That needs the two sides to be disjoint. The faces across both walks are
`f` and `Π`, so a face-class chain on the side of one walk never crosses an edge of the other.
Nothing on origin states this. `ExtPhiData.disjoint_sideFaces_of_twoGon` is specific to the
Lemma 9.3 two-gon and has a different conclusion (no other region meets the side).

CLAIM separation of the sides of two closed walks with barrier faces, GroupApproximation/GGT/VanKampen/SimpleClosedWalkSidesDisjoint.lean

## Log

- 17:05: claim landed. The module is written and probed next.
- 17:18: probe 0913-171645-22733 GREEN. It built the module with no warnings, and all five
  `#audit_axioms` report only `[propext, Classical.choice, Quot.sound]`.
- 17:24: LANDED d58c49132, with the bytes checked against the green record (md5 fe11b103). It is
  queued for wiring.
  - `disjoint_sideFaces_of_across`: the sides are disjoint when the faces across each walk are
    off the side of the other and no edge of `w₂` is an edge of `w₁`.
  - `not_mem_sideFaces_or_of_across`: any face, the exterior face included, is off one side.
  - `disjoint_sideFaces_of_barrier`: the same for simple closed walks with the same barrier faces.
  - `mem_sideFaces_iff_of_eqvGen` and `eqvGen_walkKeep_of_mem_sideFaces`: the face-class steps.

CLAIM noncrossing barrier sides and the no-common-dart variant, GroupApproximation/GGT/VanKampen/SimpleClosedWalkSidesDisjoint.lean (additive, same module)

- 17:35: the extension is written.
  - `not_walkKeep_of_across` and `disjoint_sideFaces_of_across_of_not_mem`: a dart of `w₂`
    reversed on `w₁` contradicts the first barrier condition, so no common dart is enough.
  - `disjoint_sideFaces_of_barrier_noncrossing` and `not_mem_sideFaces_or_of_barrier_noncrossing`:
    the barrier version for noncrossing closed walks. The dichotomy gives the input `hout` of
    `PocketRegion.ofNoncrossingClosedWalk` for one of the two walks.

- 17:36: probe 0913-173352-83225 GREEN. It built the module with no warnings, and all nine
  `#audit_axioms` report only `[propext, Classical.choice, Quot.sound]`. The module now imports
  `NoncrossingClosedWalkSides`; no module imports it, on origin or in the shared tree. The extension
  lands in the same commit as this entry. The 17:33 attic copy hit a ref-lock race and was not
  needed.

## For the producer of the relator-cell branch (not built here)

On the pocket walks `w₁ = invDarts X ++ invDarts B` and `w₂ = invDarts Y ++ invDarts A`:
- No common dart: the face walk of `f` and the carrier of `Π` have no repeated dart, and `f ≠ Π`
  (`face_not_cell`).
- The faces across `w₁` are `f` (from `X`) and `Π` (from `B`); across `w₂` they are `f` (from `Y`)
  and `Π` (from `A`). So both barrier conditions hold when `X`, `Y`, `A` and `B` are all nonempty.
  The cases with an empty window need separate handling.
- Noncrossing of the two walks is not produced here. It is one of the four facts of the ruling at
  roster l.949 (jacobson).
