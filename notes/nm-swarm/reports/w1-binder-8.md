# Lane w1-binder-8: GeodesicCollarStatement (W1 waist binder 8), independent second start

Lead: session nonsofic-existence-49 (wave 2, `notes/nm-swarm/reports/ct-lead.md`).

## Binder state on origin (checked 2026-09-13 ~16:55 at 835fa3ee5)

- `GeodesicCollar.geodesicCollarStatement_of_strip (hstrip : StripStatement) : GeodesicCollarStatement`
  (hull-bridge, SurgeryGeodesicCollarReduction, 43f028873).
- `GeodesicCollar.stripStatement_of_step (hstep : StripStepStatement) : StripStatement`
  (simple-group, SurgeryGeodesicCollarInduction, cec4605ee).
- So binder 8 rests on ONE Prop, `GeodesicCollar.StripStepStatement`: a strip along `p` whose remaining
  walk starts with `d` has a transport to a strip along the image of `p ++ [d]`.
- kh-torsion is assigned the step (roster rulings ~16:00–16:17) and registered
  `GGT/VanKampen/SurgeryGeodesicCollarPinch.lean` at 15:45. No such file exists on disk or on origin at ~16:55.

## CLAIM

CLAIM StripStepStatement (second start, distinct declaration names) GroupApproximation/GGT/VanKampen/SurgeryGeodesicCollarStripStep.lean

Declaration names are chosen so that they cannot collide with kh-torsion's module: namespace
`GroupApproximation.GGT.VanKampen.GeodesicCollar.StripStep`, endpoint
`GeodesicCollar.StripStep.stripStepStatement_holds : StripStepStatement`.

## Route

1. `d` is not a loop: the walk `p ++ d :: r` has at least two darts (`vertexOf_alpha_ne_of_mem`), so the face `f` of `d` has
   at least two darts. `d` is not in the strip face (`p ++ q` is its face cycle, and `d ∉ p ++ q`).
2. Double `d` in `f` (`FaceEdgeDoubling.diagram`, `collarTransport`): the digon `[d, none]` is a G-face of the face set.
3. Pinch at `x = alpha (last p)` and `y = alpha none` (`PinchSplit.Input`): both lie at the vertex where the walk leaves along
   `d`. The merged face is `last p :: d :: none :: (q ++ dropLast p)`, a rotation of `p ++ [d] ++ none :: q`. It is not a relator
   face and not the exterior.
4. The face set becomes the `kept` image. The boundary darts are unchanged, the walk stays simple (`isSimpleClosedWalk_pinch`),
   and the new strip has `q' = none :: q`.
5. Transport = doubling transport, then the identity-on-darts pinch transport.

## BINDER 8 CLOSED (2026-09-13 ~18:10)

- LANDED c8c512bbd, probe 0913-180704-2462 GREEN (`BUILT GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep`).
- Closed endpoints, each `#audit_closed_axioms` = [propext, Classical.choice, Quot.sound]:
  - `GeodesicCollar.StripStep.stripStepStatement_holds : GeodesicCollar.StripStepStatement`
  - `GeodesicCollar.StripStep.stripStatement_holds : GeodesicCollar.StripStatement`
  - `GeodesicCollar.StripStep.geodesicCollarStatement_holds : GeodesicCollarStatement`
- Wiring: queued in `wire-queue.txt`. The module imports `SurgeryGeodesicCollarInduction` (not in the root yet) and
  `SurgeryGeodesicCollarReduction`.
- Consumers: any `GeodesicCollarStatement` binder (waist binder 8 of
  `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals`, and the section pocket cut residuals) can take
  `GeodesicCollar.StripStep.geodesicCollarStatement_holds`. The binder flip belongs to the waist owners; this lane edits
  none of their files.

## Module (2026-09-13 ~17:40, draft preserved at attic 677af02a3)

`GroupApproximation/GGT/VanKampen/SurgeryGeodesicCollarStripStep.lean`, namespace `GeodesicCollar.StripStep`:

| declaration | content |
|---|---|
| `rotate_merged`, `vertexOf_alpha_getLast` | list and walk helpers |
| `not_mem_face`, `faceOf_getLast`, `faceOf_ne` | the next dart is off the strip face |
| `kept_mem_faceSet_iff_of_mem`, `isBoundaryDart_faceSet_iff_of_mem`, `pinchTransport` | a pinch whose face set contains both pinch faces keeps the boundary and is a transport |
| `digonCycles`, `digonInput`, `leftFace_mem`, `rightFace_mem`, `pinchStrip`, `stripStep_of_digon` | pinch of the strip face with a G-digon `[d, n]` gives the strip along `p ++ [d]` |
| `isFaceCycle_embed`, `faceOf_head_ne`, `doubleStrip` | the strip survives doubling the next dart |
| `stripStepStatement_holds : StripStepStatement` | closed endpoint |
| `stripStatement_holds : StripStatement` | via `stripStatement_of_step` |
| `geodesicCollarStatement_holds : GeodesicCollarStatement` | binder 8, via `geodesicCollarStatement_of_strip` |

Coordination: ms-inverses-1 and ms-core-2 offered to take step 1 and steps 3–4 respectively. Both were
declined because the code was already on disk.

## Binder 3 (main, ~18:15): OsinLemma94CaseOneRCellStatement, relator-cell branch

CLAIM closed dart walks of the Case 1 pocket walks and the simple-shape X-pocket producer, GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellSimplePocket.lean

- Split sent to w1-binder-3 (one message, naming ms-intro-1). This lane: `SameCellSimplePocket.isClosedDartWalk_X` and `_Y`, then a proof of `OsinLemma94CaseOneSimplePocketStatement` (ms-intro-1 states it), plus the Y mirror. w1-binder-3: noncrossing, outer FollowsBoundary, Euler and the assembly. ms-intro-1: the shape reduction and shapes 1–3.

- LANDED 1d23a20e8: `Estimating/OsinLemma94SameCellPocketWalk.lean`, probe 0913-182915-47292 GREEN, BUILT. Namespace `SameCellPocketWalk`: `IsWalkFromTo` with `append`, `reverse_map`, `exists_split`, `eq_of_ne_nil`, `isClosedDartWalk`; `exists_isWalkFromTo_faceBoundary_rotate`; `exists_window_walks`; `isClosedDartWalk_X : IsClosedDartWalk (invDarts X ++ invDarts B)` and `isClosedDartWalk_Y`, over htrav, hPi, `0 < sourceArc.length`, `0 < targetArc.length` and nonemptiness. Queued for wiring.
- In probe: `Estimating/OsinLemma94SameCellSimplePocket.lean` (attic c43b9463b): `SameCellSimplePocket.false_of_simpleWalk_of_below` (walk-level kill, as ms-intro-1 asked), `false_of_simplePocket_X`, and the closed `osinLemma94CaseOneSimplePocket : OsinLemma94CaseOneSimplePocketStatement`.

CLAIM noncrossing, outer FollowsBoundary and Euler for the Case 1 pocket walks without spur (facts 1, 3, 4 of the binder-3 ruling; jacobson is down and main reassigned the facts), GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellPocketNoncrossing.lean

- Route: the complement spelling `c = B ++ X` is a first-turn walk. Face steps inside `B` and `X` turn in one step; the junction `last B -> head X` passes `head p` and the closing turn `last X -> head B` passes `alpha (last q)`, both off the walk edges; empty windows give three-step turns. `firstTurnWalkPocketInputs` then gives all three facts for `invDarts X ++ invDarts B` (and the Y mirror). A walk with a spur is never noncrossing, by definition, so the no-spur hypothesis is exact.
