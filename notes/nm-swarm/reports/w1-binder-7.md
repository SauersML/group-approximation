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
- **LANDED 514e47490** `Estimating/OsinPocketFullArc` (probe 0913-180300-88794: BUILT and COMPILED; the co-probe was red
  only on ArcTrim). The module is unwired and queued for wiring.
  - `PocketFaceSet.not_simple_of_full_sourceArc K hfull hrest : ¬ K.Simple`, where hfull is
    `K.sourceArc.length = (cellDarts X K.source).length` and hrest is
    `K.firstSide ++ K.secondSide ++ K.targetArc.darts ≠ []`.
  - `PocketFaceSet.not_simple_of_full_targetArc K hfull hrest`, where hfull is `K.targetArc.length = (outerDarts X).length`
    and hrest is `K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ≠ []`.
  - Helpers: `PocketFullArc.cyclicRel_rotate`, `darts_eq_rotate_of_full`, `outerDarts_chain`, `outerDarts_cyclic`,
    `closes_mem`, `mem_getLast?_append_singleton`, `PocketFaceSet.invDarts_eq_tail_append`.
  - Calibration: `PocketFullArc.wrapK_not_simple` passes `#audit_closed_axioms`.
  - The first probe (0913-175113-42314) was red on deprecated option lemmas and two simp goals, since fixed.
- **LANDED d5821cd77** `Estimating/OsinPocketArcTrim` (probe 0913-180605-99266 GREEN, BUILT and COMPILED). The module is
  unwired and queued for wiring.
  - `CyclicArc.dropLastArc`, `CyclicArc.tailArc` and their `_darts` lemmas.
  - `PocketFaceSet.trimSourceLast K hlabel hne hroom`, with `hroom : K.firstSide.length < eps`.
  - `PocketFaceSet.trimTargetHead K hlabel hne hs hroom`, with `hs : K.targetArc.start.1 < (outerDarts X).length` and
    `hroom : K.secondSide.length < eps`.
  - `closedWalk_`, `repeatedVisits_` and `simple_..._iff` for both trims: the cycle is unchanged.
  - `trimSourceLast_sourceArc_lt` and `trimTargetHead_targetArc_lt`: the trimmed arc is not full.
  - The first co-probe (0913-180300-88794) was red on one decomposition goal, since fixed.
- **Re-decomposing inside `X` is not a proof route (paper, 2026-09-13 ~18:20).**
  - Instance: the long rose over `F(a,b)` at `ε = 1`, `N = 3`.
    - `Π = aᴺ` and `R = bᴺ`, each with `N` darts. The exterior is a single dart labelled `c = aᴺbᴺ`.
    - `κ` is a G-face whose walk is `inv(∂Π)`, the `c`-loop, `inv(∂R)`, all at one vertex `v`.
    - `K = {κ, R}`: source `Π`, `t₁ = ∂Π`, `t₂ = [c]`, empty sides.
  - No face set of `X` is a simple pocket face set:
    - `{Π}` or `{R}`: both arcs empty, and the sides would need `N > 2ε` darts;
    - `{κ, R}` or `{κ, Π}`: the boundary is a closed cycle through `v` plus the `c`-loop at `v`, so every walk order visits
      `v` twice;
    - `{κ, Π, R}` has no source, and `{κ}` has no kept cell.
  - Both lobes of `K` fail:
    - the pocket side of `inv(∂Π)` contains the exterior;
    - the pocket side of the `c`-loop holds every relator cell.
  - A rebuilt O-equivalent copy does rescue it: `F′ ∋ R`, bounded by `[c]`, `N − 1` darts of `Π`, and `[a]`, with the sides
    exactly those produced by `trimSourceLast` and `trimTargetHead`.
  - So the innermost-circuit rescue of ms-cite-1's record 5f21c733e does not prove the Pos binder, and the step has to build
    copies: trim, double the trimmed side dart, split.
- **LANDED b2c347f69 `Estimating/OsinPocketTrimDouble`** (probe 0913-183017-52812 GREEN, BUILT and COMPILED; unwired, queued
  for wiring), the first stage of the wrap-case step:
  - `PocketFaceSet.exists_trimDouble K hlabel hne hroom hlen hK`: first `trimSourceLast`, then hull-respell's
    `faceEdgeDoubling` at the source face on the trimmed dart. After the trim that dart is off the source arc, which supplies
    `hsrc`.
  - The output is an O-equivalent copy with letter labels and a pocket face set in walk order in the same positions: same
    repeated visits, a source arc one dart shorter, and a first-side dart whose across-face is the new digon. The digon is a
    G-face that is not the exterior, not a relator face, and not in the face set.
  - Rotation at the junction vertex `p` after the doubling (paper, from `EdgeInsertion.toCombMap`): `embed x → none →
    embed(head t₁)`, where `x = α(last t₁)`. The corner after `embed x` is the digon, so `embed x` is a legal split dart
    `I.x`.
  - Still open: the second split dart. It needs a G-corner outside the face set in the other gap at `p`, for the wrap shape
    with `t₂` full (the exterior corner, through kh-cckw's outer spur thickening), and the StretchAvoids chain.
- ms-intro-4 (binder 5, `CellPocketPinchPosStatement`) imports ArcTrim and FullArc; their helper names stay fixed. There is
  no generic boundary-cycle layer, and `exists_trimDouble` is at `PocketFaceSet` level.
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
