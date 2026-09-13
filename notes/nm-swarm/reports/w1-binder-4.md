# w1-binder-4

Lane `w1-binder-4` (session nonsofic-existence-49, wave 2): an independent second start on binder 4 of the post-(A) W1
waist, `OsinTwoGonHoldsSectionStatement` (C6′ of Osin's Lemma 9.3). The owners are debt-conditional, baseline-debt,
hs-vanishes and sec2-sentences. This lane never edits their files.

## CLAIM

CLAIM C6′ uniform noncrossing route `GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonNoncrossingRoute.lean`

- `TwoGonNoncrossingPocketInput`: the geometric content of C6′ as one named Prop. For the labels of a two-gon (exterior
  regions `a ≠ b` of one cell targeting one section, `a`'s target arc before `b`'s), there is a noncrossing closed walk
  `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` whose outer cycle follows its boundary, with the
  exterior face off its side, `a` and `b` on its side, no relator cell on its side, and no other selected region
  meeting it.
- `twoGonHoldsInput_of_noncrossingPocket`: `TwoGonHoldsInput` from that Prop, through `exists_twoGonLabels`,
  `PocketRegion.ofNoncrossingClosedWalk` and `emptyTwoGonInput_holds`.

## Why this route

- `emptyTwoGonInput_holds` (fff-periodic, `OsinPocketDiscEmptyTwoGon`) collapses the pocket through its disc region, and
  its docstring says the pocket may be pinched. `PocketRegion.ofNoncrossingClosedWalk` (dgo-analytic) builds a pocket
  region from a noncrossing walk whose outer cycle follows. So C6′ needs no split into simple and pinched walks.
- The planned module 4 (debt-conditional report) splits on simplicity and sends the pinched branch to the pinch Prop.
  baseline-debt's report records that `PocketPinchLabelledStatement` needs a kept relator cell, which `hno` forbids,
  and that question is open with the lead. The noncrossing route bypasses it.
- The Euler input comes from hull-euler's `IsNoncrossingClosedWalk.reclosed_euler`. `hw` and `hfollows` come from
  hull-select's `firstTurnWalkPocketInputs` once the complement spelling is a first-turn walk; that walk excludes the
  lake (`OsinPocketFirstTurnWalkModel`).

## Residual

- The first-turn property of the complement spelling of the two-gon pocket walk. sec2-sentences owns the first-turn
  producer for `K.walk` (roster ruling ~16:10), so this lane consumes it and does not rebuild it.
- `a.1, b.1 ⊆ side`, `hno`, `havoid` on the rotated walk: module 3 (debt-conditional, `TwoGonWalkHyp`) or absorption
  (sec2-sentences).

## Progress log

- 2026-09-13 ~17:05: claim landed before writing.
