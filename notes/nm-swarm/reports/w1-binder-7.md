# w1-binder-7 lane report

A lane of session nonsofic-existence-49, wave 2: an independent second start on binder 7 of the post-(A) W1 waist,
`PocketPinchLabelledStatement` (`Estimating/OsinPocketPieces.lean:272`). The owners are hull-respell, kh-cckw,
go-lemma42, ghw-assembly and audit-sec3. This lane never edits their files.

## 2026-09-13 ~17:05: state found

- The binder is FALSE as stated. dgo-geometric's `OsinPocketWrapRose.pocketPinchWrapRefutation` (6dfa779fe, 87358b0ad; probe
  0913-163031-39703 GREEN) proves `¬ PocketPinchLabelledStatement.{0,0,0}` and `¬ PocketPinchStepStatement.{0,0,0}`.
  The witness is a three-petal rose at `ε = 0` whose relator words and boundary word have one letter.
- Every assembly that consumes the binder therefore consumes a false Prop: `sectionPocketCutInput_of_pieces`,
  `osinSectionPocketCutSection_of_residuals`, `OsinDescentResiduals` and `OsinGreendlingerOpenResiduals`.
- dgo-geometric named two untested repairs, a `0 < ε` binder and long relators, and left the choice to the lead. There is no
  roster ruling since 16:17, and ghw-assembly has parked the wrap case.

## CLAIM

- CLAIM binder-7 repair interface (`0 < ε`): `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketPinchPositive.lean`
  (new module).
  - `PocketPinchLabelledPosStatement` and `PocketPinchStepPosStatement` state the binder and the step with `0 < eps` added.
  - The implications from the unrepaired Props, and the step induction at `0 < eps`.
  - `sectionPocketCutInput_of_residualsPos` and `osinSectionPocketCutSection_of_residualsPos` (threshold `max eps0 1`),
    so the section-level consumer needs only the repaired binder.
- CLAIM evidence that the refutation does not transfer: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketWrapRoseRescue.lean`
  (new module). On dgo-geometric's `wrapDiagram`, for every `ε ≥ 1` the face set `{R}` with `s_1 = [5]` and empty arcs is a
  simple pocket face set in positions `0..1`.

## LANDED 1b4736bcb (probe 0913-170902-87292 GREEN, BUILT and COMPILED for both modules)

Both modules are new and unwired, and are queued for wiring. They certify no printed sentence, so they add no census row.

- `Estimating/OsinPocketPinchPositive`:
  - `PocketPinchLabelledPosStatement` and `PocketPinchStepPosStatement`: the binder and the step with `0 < eps`.
  - `pocketPinchLabelledPosStatement_of_labelled` and `pocketPinchStepPosStatement_of_step`: the old Props give the repaired ones.
  - `pocketPinchLabelledPosStatement_of_stepPos`: hull-respell's induction at `0 < eps`.
  - `sectionPocketCutInput_of_residualsPos` (takes `heps : 0 < eps`).
  - `osinSectionPocketCutSection_of_residualsPos hfaces hpinch hgeodesic : OsinSectionPocketCutSectionStatement`, at
    threshold `max eps0 1`.
- `Estimating/OsinPocketWrapRoseRescue`:
  - `rescueK eps heps` and `rescueK_simple`;
  - `wrapRoseRescue : WrapRoseRescue`, which passes `#audit_closed_axioms`.

## LANDED 4db9c6729 (probe 0913-171243-3240 GREEN, BUILT and COMPILED)

- `Estimating/OsinDescentResidualsPos`: `osinDescentSection_of_residualsPos` and
  `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos`, the two assemblies of `OsinDescentResiduals` with the repaired
  pinch. The module is unwired and queued for wiring.

## 2026-09-13 ~17:35: after the lead restart, the wrap residual

- CLAIM, the full-arc characterization of the wrap case: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFullArc.lean`,
  a new module.
  - `PocketFaceSet.not_simple_of_full_sourceArc`: in ANY diagram, a pocket face set whose source arc is the whole cell cycle is
    not simple, unless its cycle is that reversed arc alone.
  - `PocketFaceSet.not_simple_of_full_targetArc`: likewise when the target arc is the whole exterior cycle, unless the cycle is
    that arc alone.
  - Consequence: the wrap case is exactly a full arc with a nonempty remainder. Doublings and splits transport arcs and sides
    and keep a full arc full, so no transport-based step closes it. The step has to re-decompose the walk.
- CLAIM, the trims at `0 < eps`, in a second new module after that one: move one dart of an arc into a side with room. The
  cycle is unchanged, so walk order and repeated visits are unchanged, and the data stop being wrap data.
- Agreed with ms-intro-4, which takes "first-turn order survives the edge doublings" in
  `Estimating/OsinPocketEdgeDoublingFirstTurns.lean`.
- Agreed with ms-inverses-2:
  - (A) first-turn model tests on the rose, `Estimating/OsinPocketWrapRoseFirstTurn.lean`;
  - T2, first-turn order across the exterior spur thickening (`OsinPocketOuterSpur`). T1 and T1′ belong to ms-intro-4.
- Agreed with ms-cite-1: it runs the counterexample search for `PocketPinchLabelledPosStatement` at `ε ≥ 1`
  (`Estimating/OsinPocketPinchPosModels.lean`). This lane keeps the positive route.
- In flight: `Estimating/OsinPocketFullArc` (attic 33e4d51f6) and `Estimating/OsinPocketArcTrim` (attic 06cb6c7cd).
  - The first probe of FullArc (0913-175113-42314) was red: deprecated option lemmas, and two simp goals on reversed
    arcs and `getLast?`. Fixed and re-probing together with ArcTrim.
  - ArcTrim: `trimSourceLast` (first side shorter than `ε`) and `trimTargetHead` (second side shorter than `ε`, arc
    not at the wrapped start). Face set and cycle are unchanged, so walk order, repeated visits and simplicity are
    unchanged, and the trimmed arc is not full.
- Where the step route sticks: a full arc with a nonempty remainder and both sides at length exactly `ε`. No trim has
  room, and transport surgery keeps arcs and sides. This does not refute the Prop, since the conclusion may change the
  source, the kept cell, the arcs and the sides.

## For the waist owner (ghw-assembly), through the lead

The one-line swap in `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals` (`OsinGreendlingerOpenResiduals`):
- replace binder 7 `hpinch : PocketPinchLabelledStatement` with `hpinch : PocketPinchLabelledPosStatement`;
- call `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos` instead of `_of_residuals`.

That removes the false binder from the waist. hull-respell's step route then targets `PocketPinchStepPosStatement` through
`pocketPinchLabelledPosStatement_of_stepPos`. The `ε ≥ 1` truth of the repaired pinch is not settled in general. The rose is
only the known counterexample shape, and it is rescued.
