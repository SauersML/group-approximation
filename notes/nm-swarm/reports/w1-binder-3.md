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

- 17:45: main's next item is the empty-window cases (X, Y, A or B empty), where the barrier
  conditions of `disjoint_sideFaces_of_barrier_noncrossing` fail. Split agreed directly with
  ms-intro-1: it takes the pinch split (OsinLemma94SameCellPocketPinch); this lane takes the empty
  windows.
- Finding: side selection needs no split on empty windows.
  - Every dart of either pocket walk has `f` or `Π` across it.
  - The first edge of `p` joins `Π` to `f` and lies off both walks.
  - A noncrossing walk keeps the face across each of its darts off its side. So `f` and `Π`, which
    are in one face class of the walk, are both off its side, whether X, Y, A, B are empty or not.
  - The barrier conditions then hold, and the no-common-dart variant gives disjoint sides and the
    exterior-face dichotomy.

CLAIM the pocket sides of the Case 1 same-cell walks in every window case, GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellPocketSides.lean

- 18:05: probe 0913-180324-90857 GREEN. `OsinLemma94SameCellPocketSides` built with 0 warnings. All
  17 `#audit_axioms` are within `[propext, Classical.choice, Quot.sound]`; one of them is
  `[propext, Quot.sound]`. The module lands in the same commit as this entry.
  - Generic layer, in namespace `SimpleClosedWalkSides`:
    - `mem_sideFaces_iff_of_not_walkKeep`;
    - `not_mem_sideFaces_of_two_faces`: a noncrossing walk with two faces across it and an edge
      between them off the walk has both faces off its side;
    - `faceOf_alpha_eq_or_of_alpha_mem` and `not_walkKeep_of_alpha_mem`;
    - `disjoint_sideFaces_of_two_faces` and `not_mem_sideFaces_or_of_two_faces`.
  - Case 1 layer, in namespace `SameCellPocketSides`, over the binders of
    `OsinLemma94CaseOneRCellStatement` (`htrav`, `hPi`, `0 < sourceArc.length`):
    - `exists_edge`: the first dart of `p`;
    - `not_mem_walk_of_mem_walk`: the pocket walks share no dart;
    - `face_not_mem_sideFaces_X` and `_Y`: `f` and `Π` are off the side of each noncrossing pocket
      walk. `Π` off the side is the input `hi` of `false_of_pocketRegion_of_below`;
    - `disjoint_sideFaces` and `not_mem_sideFaces_or`: the exterior face is off one side, which is
      the input `hout` of `PocketRegion.ofNoncrossingClosedWalk`.
  - No barrier nonemptiness is assumed, so X, Y, A or B empty are covered as they are.
- Which empty windows occur (read from the definitions; no least-area model built):
  - `Maximal` allows two consecutive sides of the same cell when the walk across turns away at the
    common vertex, and it does not constrain the wrap pair. So X = [] and Y = [] can occur.
  - B = [] and A = [] mean that `q` and `p` are consecutive on the carrier of `Π`.
  - In the relator-cell branch X ++ B and Y ++ A read values other than 1, so both are nonempty.
    The value-one kills cover the other cases.
  - Not settled here: whether a degenerate walk, such as `invDarts B` alone when X = [], is
    noncrossing. That belongs with jacobson's four facts.

## For the producer of the relator-cell branch (not built here)

On the pocket walks `w₁ = invDarts X ++ invDarts B` and `w₂ = invDarts Y ++ invDarts A`:
- No common dart: the face walk of `f` and the carrier of `Π` have no repeated dart, and `f ≠ Π`
  (`face_not_cell`).
- The faces across `w₁` are `f` (from `X`) and `Π` (from `B`); across `w₂` they are `f` (from `Y`)
  and `Π` (from `A`). So both barrier conditions hold when `X`, `Y`, `A` and `B` are all nonempty.
  The cases with an empty window need separate handling.
- Noncrossing of the two walks is not produced here. It is one of the four facts of the ruling at
  roster l.949 (jacobson).

## Item 3: binder 5 residual (2), `hout` for the cell pocket walk (main's 18:4x assignment)

Ownership check, 18:45: ms-intro-4's residual list (a0ef02fff, report item 3) leaves `hout` undecided.
ms-inverses-2's in-flight `OsinPocketCellKeptCellNoncrossing` and ms-cite-1's `OsinPocketMultipleEdgeCopy` consume
`hout` as a hypothesis. No file on origin or in the shared tree produces it or picks the order of the two regions.

Finding: `hout` for a fixed order of the two regions can fail, lake or no lake.
- `CellPocketWalk.exists_of_joinsCells` is symmetric in `a` and `b`, but its walk is not. Its first arc spans the arc of
  `a`, the gap `G₁` of `Π_i` after it, and the arc of `b`, in carrier order.
- The walk darts along `G₁` reverse darts of `Π_i`, so their own faces are the faces across `G₁`: the pocket next to `G₁`.
  The side darts are boundary darts of `a` and `b`, so the side of the walk holds `a`, `b` and that pocket.
- Swapping `a` and `b` replaces `G₁` by the other gap of `Π_i`, and so the pocket by the complementary pocket. The
  exterior face lies in at most one of the two pockets.
- If a dart of `G₁` has the exterior face across it (`Π_i` touches `∂Δ` between the two arcs), the exterior face is the
  own face of a walk dart, so it lies on the walk's side and `hout` fails for that order.
- The lake model is a different obstruction, to following outer cycles. Its cell is a monogon, which cannot carry the two
  disjoint nonempty region arcs.
- The premise needed is a choice of order: `hout` for the walk of `(a, b)` or for the walk of `(b, a)`.

CLAIM the exterior face against the cell pocket walk and the two-order statement, GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkOuter.lean

- 18:40: main named the target: `CellPocketWalkOuterOffSideStatement` (ms-cite-1, eb678c70a,
  `Estimating/OsinPocketMultipleEdgeCopy`), consumed by `OsinGreendlingerResidualsV2Copy`.
- It is NOT discharged; it looks over-strong.
  - It quantifies over an arbitrary order `(a, b)`, with `CopyClean a b`, and fixes the walk of that order.
  - `CopyClean` constrains only the sides of the walk and the cells. Nothing constrains the faces across the gap darts of
    `t_1` and `t_2`.
  - The walk darts along a gap reverse cell darts, so the faces across the gap are on the walk's side.
  - So the statement forbids `Π_i` (or `Π_j`) from touching `∂Δ` between the arcs of `a` and `b` in carrier order. Its
    hypotheses (least area, a globally distinguished family, CopyClean, closed walk, nodup, no reversed dart) do not give
    that.
  - The reduction is proved. No least-area diagram realizing such a gap is built, so this is not a refutation.
- 18:46: probe 0913-184416-19758 GREEN. `OsinPocketCellWalkOuter` built with 0 warnings, and all five `#audit_axioms`
  report only `[propext, Classical.choice, Quot.sound]`. The module lands in the same commit as this entry.
  - `CellPocketWalk.faceOf_alpha_mem_sideFaces_of_mem_arc`: the face across a dart of `t_1` or `t_2` is on the side.
  - `CellPocketWalk.outerFace_mem_sideFaces_of_mem_arc`: when that face is the exterior face, `hout` fails.
  - `CellPocketWalk.not_outerFace_across_arc_of_outerOffSide`: `CellPocketWalkOuterOffSideStatement` implies that no
    dart of `t_1` or `t_2` has the exterior face across it.
  - `CellPocketWalk.two_le_length_cellDarts_first` / `_second`: both carriers have at least two darts, so the monogon cell
    of the lake model carries no pocket walk. The lake obstructs following outer cycles, not `hout`.
- Proposed correction (for ms-cite-1 and main to decide; not landed):
  - Pick the order. The walk of `(b, a)` spans the complementary gaps, so its side holds the complementary pocket.
  - The residual is then: the exterior face is off the side of the walk of `(a, b)` or off the side of the walk of
    `(b, a)`, for noncrossing walks of both orders. Every region face is not the exterior face
    (`FaceSetBoundary.all_gCells`).
  - A proof would track the four sides and four gaps, which are exactly the edges where the two sides differ. It is not
    built.
- `CellPocketWalkSideRelatorCellStatement` (same file, same fixed order) may have the same issue: the side of the fixed
  order holds the pocket after the first gap, and the relator cells may lie in the other pocket. Not checked here.

## Item 4: the two-order dichotomy (main's 19:0x assignment, ruling "choose the order" accepted)

Target: for noncrossing walks `w₁` (order `(a, b)`) and `w₂` (order `(b, a)`), the exterior face is off the side of
one of them. ms-cite-1 lands the respelled residuals; this lane discharges them by name once it sends the names.

CLAIM the two-order dichotomy:
- `GroupApproximation/GGT/VanKampen/CyclicArcComplement.lean`: two arcs of a duplicate-free cycle spanning `P G₁ Q`
  and `Q G₂ P` have disjoint gaps `G₁`, `G₂`.
- `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkOrder.lean`: a face on both sides is a face of `a` or
  `b`, so by `FaceSetBoundary.all_gCells` the exterior face is off one side.

Proof plan, and the case analysis used as the model test:
- Take a face-class chain of `w₁` from a walk dart to the face. Carry along it the invariant "on the side of `w₂` ⇒ in
  `a ∪ b`". Every face on the chain is on the side of `w₁`.
- Across an edge on neither walk, membership in the side of `w₂` is preserved. Membership in `a` and in `b` is
  preserved too: every boundary dart of `a` or `b` lies in `inv(arc on i)`, `sideFrom i`, `inv(arc on j)` or
  `sideFrom j`, and each of these is on `w₁` or `w₂`.
- Across an edge of `w₂` only, the dart is a side of `w₂`, whose own face is in a region. Otherwise it is a gap dart of
  `w₂`, whose other face is `Π_i` or `Π_j`. Both cells are off the side of `w₁`, so that step cannot occur on the chain.
- Base case at a gap dart of `w₁`:
  - if the edge is on neither walk, `Π_i`, off the side of `w₂`, shares its face class;
  - if the dart lies on a side of `w₂`, its own face is in a region;
  - the case of a gap dart of `w₂` needs the gaps disjoint (first module);
  - the other cases contradict the arcs having no repeated dart, or the cells being distinct.
- No `CopyClean` field is used.
- 19:5x: ms-cite-1 respelled the residual to the shape agreed here: `CellPocketWalkOuterOffSideSomeOrderStatement`
  (da5b1466e, `Estimating/OsinPocketMultipleEdgeCopy`).
  - The complementary order is `(b, a, i, j)`, not `(b, a, j, i)`. The order `(b, a, j, i)` spells the same walk as
    `(a, b, i, j)`, up to rotation.
  - The statement needs no CopyClean and no least area.
  - Its consumers are `multipleEdgePocketRegionCopyInput_of_pinchOrder` and its successors, `OsinGreendlingerWaistV4`
    and `TorsionFreeResidualsV4`.
- The first two probes were red (0913-193144-68949, 0913-194106-15623). Fixes:
  - the identifiers `hΠ…` do not parse, because `Π` is a binder token; they are renamed `hcells`, `hoffi₁`, and so on;
  - `isNoncrossingClosedWalk_of_orient` lives in `OsinPocketColourNoncrossing`, and the import now names that module;
  - the local copy of `mem_invDarts_iff` is dropped in favour of `Embedded.mem_invDarts_iff` (FaceSetBoundaryWalk).
  Both failed probes wrote `.green` records. Those records are not evidence.
- 20:33: probe 0913-202753-83639 GREEN.
  - `OsinPocketCellWalkOrder` built with 0 warnings, and all 12 `#audit_axioms` report only
    `[propext, Classical.choice, Quot.sound]`.
  - `CyclicArcComplement` was restored from cache with the md5 it had when built at 0913-193144-68949. Its two audits
    there report the same three axioms.
  - Both modules land in the same commit as this entry.
  - `GGT/VanKampen/CyclicArcComplement`:
    - `CyclicArc.rotate_eq_of_head?_eq_of_nodup`;
    - `CyclicArc.not_mem_of_complementary_spans`: on a cycle with no repeated dart, arcs reading `P G₁ Q` and
      `Q G₂ P`, with `P` and `Q` nonempty, have disjoint gaps.
  - `Estimating/OsinPocketCellWalkOrder`:
    - `CellPocketWalkOrder.mem_regions_of_mem_sideFaces_both`: for noncrossing walks of both orders, a face on both
      sides is a face of `a` or `b`. The proof carries a face-class invariant along a chain of `w₁`.
    - `CellPocketWalkOrder.outerFace_not_mem_sideFaces_or`: so the exterior face is off one of the two sides
      (`FaceSetBoundary.all_gCells`).
    - `CellPocketWalkOrder.outerFace_not_mem_sideFaces_or_of_walks`: the same from the walk data and closed-walk facts of
      both orders, with noncrossing from `CellPocketWalkColour.walk_orient`.
    - `cellPocketWalkOuterOffSideSomeOrder : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v}`: the discharge by
      name.
  - No CopyClean field and no least area are used.
- The closed-walk facts of the `(b, a, i, j)` walk on the clean copy come from ms-cite-1's
  `CellPocketCopyCleanBothOrdersStatement` (owner w1-binder-5), not from this lane.

## Item 5: first-turn order of the section and cell pockets (main's 20:4x item; resumed 21:22 and 23:12, with w1-binder-4's cell mirror)

Origin at 23:18 (096d9219c):
- w1-binder-7 landed `SectionPocketFaceSetFirstTurnInput` and `OsinSectionPocketFaceSetFirstTurnSectionStatement`
  (`OsinPocketPinchFirstTurnAssembly`). The Input asks for `K.FirstTurns ∧ K.sourceArc.length < |∂Π|`. This lane
  targets it as spelled.
- The cell pinch Input `CellPocketPinchSectionInput` (ms-intro-4) still takes walk order.

Model test: w1-binder-4's `OsinPocketCellFirstTurnsLakeModel` (attic 8dea85688). Main's 23:12 order passes that item to
this lane.
- First-turn order is complement-side following.
  - A first turn onto an edge of the cycle is unique, so the boundary cycle must be one orbit of the first-turn
    predecessor.
  - A lake splits the predecessor into several orbits. Then no ordering of the boundary cycle is in first-turn order.
- Calibration: the multiple-edge lake and the double touch, both with monogon cells and full arcs, are not in first-turn
  order.
- A lake with proper arcs and no monogon:
  - fourteen darts, the pocket `[0,2,4,8,10]`, and the lake `{Πᵢ, H}`, which meets the rest of the complement only at `v`;
  - the walk is noncrossing and has proper arcs of both cells;
  - its predecessors split `{0,2,4}` from `{8,10}`, so no ordering is in first-turn order.
- So route (a) fails at map level even with proper arcs. Route (a) is first-turn order for the walk-order pocket of the
  orientation producer.
  - The source cell can lie in the lake, where `PocketFaceSet.absorb` does not apply.
  - A producer has to change the diagram or the face set, or rule the lake out from least area and the optimal family.
  - The models carry no labels or regions, so no producer statement is refuted.
- The section side behaves the same way. The lake walk `[0,2]` and w1-binder-6's least-area full-arc lake fail first-turn
  order.

CLAIM the lake model, landed as is under this lane after a green probe: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellFirstTurnsLakeModel.lean
CLAIM the bridge from outer following: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFirstTurnsOfOuterFollows.lean
- `FirstTurnWalk.firstTurn_prev_of_outerFollows` and `firstTurnChain_of_outerFollows`: on a noncrossing closed walk
  whose outer cycle follows its boundary, the first-turn chain of `FirstTurns`.
- `PocketFaceSet.firstTurns_of_outerFollows` and `CellPocketFaceSet.firstTurns_of_outerFollows`.
- Any producer that changes the face set until the outer cycle follows consumes it, for example lake absorption or a
  vertex split outside.
- 23:37: probe 0913-233416-59339 GREEN.
  - `OsinPocketFirstTurnsOfOuterFollows` built with 0 warnings. All 7 `#audit_axioms` are within
    `[propext, Classical.choice, Quot.sound]`.
  - `OsinPocketCellFirstTurnsLakeModel` was restored from cache with the md5 it had when built in w1-binder-4's probe
    0913-214335-23508. That log shows 14 standard audits and 0 warnings, and its direct imports are unchanged since
    that base.
  - Both modules land in the same commit as this entry.
  - `Estimating/OsinPocketFirstTurnsOfOuterFollows` (this lane):
    - `FirstTurnWalk.firstTurn_prev_of_outerFollows`: on a noncrossing closed walk whose outer cycle follows its
      boundary, the first turn from `alpha e` lands on the reversal of the walk dart before `e`
      (`IsNoncrossingClosedWalk.outerCycle_boundaryPerm_val` with `FirstTurn.of_boundaryWalk`);
    - `FirstTurnWalk.firstTurnChain_of_outerFollows` and `outerFollows_of_firstTurnChain`: the chain condition of
      `FirstTurns` on `w`, and back through `FirstTurnWalk.outerCycle_followsBoundary`;
    - `PocketFaceSet.firstTurns_of_outerFollows` and `firstTurns_iff_outerFollows`, and the same for
      `CellPocketFaceSet`.
  - `Estimating/OsinPocketCellFirstTurnsLakeModel` (w1-binder-4's bytes, attic 8dea85688, taken over on main's 23:12
    order; not edited here):
    - `FirstTurnOrder`, `FirstTurn.eq_of_walkKeep`, `FirstTurnOrder.all_or_none`;
    - the monogon calibrations `multipleEdgeLake_not_firstTurnOrder` and `doubleTouch_not_firstTurnOrder`;
    - the proper-arc lake `properLake_not_firstTurnOrder`.
- Status of the producer: BLOCKED on a choice, not refuted.
  - For a noncrossing walk-order pocket, first-turn order ⟺ outer following (proved here).
  - Outer following fails at map level on the proper-arc lake, where the source cell lies in the lake. So route (a),
    first-turn order of the orientation producer's pocket, fails for section and cell pockets alike. `absorb` needs the
    source in the exterior piece.
  - Candidate routes, for main to choose:
    1. Exclude lakes from least area and the optimal family, as a named statement that is model-tested first.
    2. Change the face set.
       - A lake holding a cell: in the cell case, absorbing the lake with the cell leaves a short side and an arc of the
         other cell, which is a loop cut with fewer cells and is killed by `OsinLoopCut.false_of_below`.
       - A lake holding no cell: `absorb`, then a Jordan-type lemma that the absorbed cycle follows.
       - A lake holding the source, section case: no kill known.
    3. Allow the pinch step to take walk order at outer pinches.
  - w1-binder-7 is formalizing `PocketFaceSet.sourceArc_lt_of_firstTurns` (first-turn order forces a proper source
    arc). Once it lands, a producer needs only `K.FirstTurns`.

## Item 6: the outer-pinch half of the pinch step (main's ruling 00:0x: route 3, change the consumer)

w1-binder-7 lands `PocketOuterPinchStepSectionStatement` and the dispatch in `Estimating/OsinPocketPinchOuterDispatch`.
The premises are walk order, `¬K.FirstTurns`, a proper source arc and a pinch. This lane proves the statement.

Gate: can the corners at an outer pinch be made G-digons? By hand, from the landed APIs.
- The split.
  - Take a turn `d₀ → e₀` whose chord is inner-adjacent: rotating from `alpha d₀`, the first keep dart is `e₀`. It
    fails its first turn once the vertex has at least two visits.
  - Cut at `x` in the outer sector after `e₀` and `y = σ⁻¹(alpha d₀)`. The corners are the faces across `e₀` and across
    `d₀`.
  - A boundary cycle in walk order is noncrossing (`BoundaryCycle.isNoncrossingClosedWalk`), so its keep darts alternate
    at a vertex.
- Corner fixes.
  - `e₀` on the source arc: double `σ e₀` (`faceEdgeDoubling`, which needs the doubled dart off the source arc).
    - If `σ e₀` were a source-arc reversal, it would be the next visit's arrival, consecutive with `alpha e₀` in the arc.
    - With a proper arc that forces `p(e₀) ≠ d₀`, a contradiction.
  - `e₀` on the target arc: thicken `σ e₀` (`outerSpurThickening`, which needs the target arc to avoid `α w_j`). This
    works by the same argument, since `outerDarts` is the exterior traversal reversed, unless the target arc is the whole
    boundary.
  - `e₀` a side dart: double or thicken `alpha e₀`, which lies off both arcs because the walk has no repeated dart.
  - Equal G-face corners: double one of them.
- Exception 1, the wrap.
  - The target arc is all of `∂Δ` and the sides meet at its endpoint vertex.
  - Both exterior darts at that corner reverse target-arc darts. No O-equivalent split exists, because merging with the
    exterior changes the boundary word.
  - Route 1's labelled test goes to main. The premise `K.targetArc.length < (outerDarts X).length`, or a named residual,
    was asked of w1-binder-7.
- Gap 2, packaging.
  - `exists_pinchStepSection_of_avoids` needs `StretchAvoids (alpha d) e` for every turn, that is, inner following at the
    split vertex. With two visits a failing turn gives it.
  - At a mixed vertex with three or more visits, an isolated-chord variant is needed. The isolated side holds no other
    keep dart, so every other turn has both endpoints on one side of the cut.
  - Vertices where all passages cross (the rose of the noninterleaving module) have no walk-order split. They stay a
    residual.

CLAIM the outer split and its invariants: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketOuterPinchSplit.lean
- the selection of an inner-adjacent failing turn, the split at the isolated chord, walk order, a proper source arc and
  fewer repeated visits (`exists_pinchStepSection_of_isolated`).
CLAIM the corner fixes and the pull-back across them: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketOuterPinchCorners.lean
