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

- LANDED 04d35a557: `Estimating/OsinLemma94SameCellSimplePocket.lean`, probe 0913-183324-66096 GREEN, BUILT, `#audit_closed_axioms` clean. Declarations: closed `osinLemma94CaseOneSimplePocket : OsinLemma94CaseOneSimplePocketStatement`, `SameCellSimplePocket.false_of_simpleWalk_of_below` (walk-level kill, consumed by ms-intro-1 and ms-inverses-1), `false_of_simplePocket_X`, `exists_rho_large`. With no relator cell the value refutes the pocket (`PocketRegion.listVal_outer_eq_one`); with one, the loop cut with the closed collar does. Queued for wiring.
- Hazard (18:39): the shared-tree copy at my landed path `Estimating/OsinLemma94SameCellPocketWalk.lean` was overwritten by a different module (walk-level islands and lobes). Origin is intact at 1d23a20e8. ms-intro-1 was told to move it; this lane removed the path from its `.files` and did not touch the disk copy.
- In probe: `Estimating/OsinLemma94SameCellPocketNoncrossing.lean` (attic 5fa0d8148): `SameCellPocketNoncrossing.pocketInputs_X` and `_Y`. For no-spur pocket walks: `IsNoncrossingClosedWalk`, outer `FollowsBoundary` and the Euler equality, over hf, htrav, hPi, hs, ht and nonemptiness.

- LANDED 0484be5e5: `Estimating/OsinLemma94SameCellPocketNoncrossing.lean`, probe 0913-190850-33126 GREEN, BUILT. Namespace `SameCellPocketNoncrossing`: `pocketInputs_X` and `pocketInputs_Y`. For a nonempty pocket walk with no dart meeting its reversal, over hf, htrav, hPi, hs and ht, they give `IsNoncrossingClosedWalk`, outer `FollowsBoundary` and the Euler equality of the reclosed side, i.e. facts 1, 3 and 4 of the binder-3 ruling. Fact 2 (hout) is w1-binder-3's `not_mem_sideFaces_or`. Route: `firstTurn_chain_X` and `firstTurn_close_X` (the complement `B ++ X` is a first-turn walk; the junctions pass `head p` and `alpha (last q)`, both off the walk edges by `not_walkKeep_head_p` and `not_walkKeep_alpha_getLast_q`, with three-step turns for empty windows), then `firstTurnWalkPocketInputs`. The Y mirror rotates the face walk and the carrier. Queued for wiring.
- Residual of this lane on binder 3: none. Open elsewhere: the assembly of `OsinLemma94CaseOneRCellStatement` (dichotomy plus X/Y pocket statements) and the shape leaves held by ms-intro-1, ms-inverses-1, ms-inverses-4 and ms-intro-3.

CLAIM the binder-3 assembly of OsinLemma94CaseOneRCellStatement over the walk-level shape leaves plus a spur residual, GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellRCellAssembly.lean

- Assigned by main at ~19:40. Interface message sent to ms-intro-1. Consumes `osinLemma94CaseOneXPocket_of_walkShapes`, `osinLemma94CaseOneYPocketOf_of_xPocketOf`, `SameCellPocketNoncrossing.pocketInputs_X` and `_Y`, `SameCellPocketSides.not_mem_sideFaces_or` and `osinLemma94CaseOneSameCell_of_rCell`. New residual: `OsinLemma94CaseOneRCellSpurStatement`.

- LANDED eb8e67fd4: `Estimating/OsinLemma94SameCellRCellAssembly.lean`, probe 0913-195034-67980 GREEN, BUILT. Queued for wiring. Declarations: `OsinLemma94CaseOneRCellSpurStatement` (the relator-cell branch where a pocket walk meets a dart together with its reversal), `osinLemma94CaseOneRCell_of_walkShapes`, `osinLemma94CaseOneSameCell_of_walkShapes`, `osinLemma94CaseOneRCell_of_residuals`, `osinLemma94CaseOneSameCell_of_residuals`, `SameCellRCellAssembly.append_ne_nil_of_listVal_ne_one`. Route: without a spur both pocket walks are noncrossing (`pocketInputs_X` and `_Y`), `not_mem_sideFaces_or` puts the exterior off one side, then the X-pocket (`osinLemma94CaseOneXPocket_of_walkShapes`) or the Y-pocket (`osinLemma94CaseOneYPocketOf_of_xPocketOf`) at shape True. The simple walk-level shape is closed by `osinLemma94CaseOneWalkSimple` (ms-intro-1, 32910e583).
- Model test of the new residual: `OsinLemma94CaseOneRCellSpurStatement` has the binders of `OsinLemma94CaseOneRCellStatement` plus one more hypothesis, and that statement is equivalent to binder 3 (docstring of `osinLemma94CaseOneSameCell_of_rCell`). So the residual follows from binder 3 and adds no falsity risk.
- EXACT residual list of binder 3 (`osinLemma94CaseOneSameCell_of_residuals`):
  1. `OsinLemma94CaseOneIslandStatement` (main list: ms-intro-1, ms-traces-2, w1-binder-2);
  2. `OsinLemma94CaseOneExcisionStatement` (ms-intro-1);
  3. `OsinLemma94CaseOneWalkCellPinchStatement` (ms-inverses-1); by `osinLemma94CaseOneWalkCellPinch_of_lobes` (79fbbbbd5) with the closed `osinLemma94CaseOneWalkCellLobeValue` it reduces to `OsinLemma94CaseOneWalkCellLobeExcisionStatement`;
  4. `OsinLemma94CaseOneWalkTouchVertexStatement` (ms-inverses-4);
  5. `OsinLemma94CaseOneRCellSpurStatement` (this lane; ms-intro-1 confirmed its shapes produce no hout for spur walks).

## Residual 5 (main ~20:15): `OsinLemma94CaseOneRCellSpurStatement`, and the `_of_enclosed` variant

CLAIM OsinLemma94CaseOneRCellSpurStatement (ms-intro-1's leaf (3)) and binder 3 over the leaves of `osinLemma94CaseOneXPocket_of_enclosed`, GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellRCellEnclosed.lean

- Planned declarations: `osinLemma94CaseOneSpur_of_rCellSpur : OsinLemma94CaseOneRCellSpurStatement -> OsinLemma94CaseOneSpurStatement` (the value-one kill when `Y A` reads 1), and `osinLemma94CaseOneSameCell_of_enclosed` over the enclosed loop cut, `EnclosedFaceSetOfNoncrossingStatement` and the spur statement.
- Spur route: a spur walk is a bridged walk. Its complement spelling `B ++ X` is a first-turn walk (the chain of 0484be5e5 never uses `alpha_not_mem`), so `EnclosedFaceSet` (bridges allowed) with the enclosed loop cut applies, once the faces enclosed by the non-bridge darts avoid f and Π and one pocket avoids the exterior.

- LANDED faa952c30: `Estimating/OsinLemma94SameCellRCellEnclosed.lean`, probe 0913-214820-73789 GREEN, BUILT. Declarations: `osinLemma94CaseOneRCell_of_noSpurPockets` and `osinLemma94CaseOneSameCell_of_noSpurPockets`. They split on a spur first, then apply the dichotomy, then the spur-free statements `OsinLemma94CaseOne{X,Y}PocketStatementOf (¬ spur)`. Also `osinLemma94CaseOneSpur_of_rCellSpur` and `SameCellRCellEnclosed.listVal_invDarts_append_ne_one`. Queued for wiring. The unprobed 20:40 draft over plain `EnclosedFaceSet` was dropped after ms-inverses-1's out-of-order refutation.

CLAIM the spur branch from the successor-form enclosed loop cut, and the combinatorial leaf `OsinLemma94CaseOneSpurEnclosureStatement`, GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellSpurEnclosure.lean

- `osinLemma94CaseOneRCellSpur_of_enclosure (hloop : EnclosedSubdiagramLoopCutSuccStatement) (hsub : ClosedWalkEnclosedSubdiagramSuccStatement) (hencl : OsinLemma94CaseOneSpurEnclosureStatement)`. The leaf: with a spur on a pocket walk, one complement spelling (`B ++ X` or `A ++ Y`) encloses an `EnclosedFaceSetSucc` avoiding Π. Its `turn_next` field is the landed first-turn chain of 0484be5e5; `mem_iff` and the exterior dichotomy are the open part.

- LANDED d3281c3b9: `Estimating/OsinLemma94SameCellSpurEnclosure.lean`. The module BUILT in probe 0913-234701-11663; the general module co-probed with it was red. Declarations: `OsinLemma94CaseOneSpurEnclosureStatement` (successor form) and `osinLemma94CaseOneRCellSpur_of_enclosure (hloop : EnclosedSubdiagramLoopCutSuccStatement) (hsub : ClosedWalkEnclosedSubdiagramSuccStatement) (hencl)`. Queued for wiring.

CLAIM the faces enclosed by a first-turn walk with bridges, GroupApproximation/GGT/VanKampen/ClosedWalkFirstTurnEnclosure.lean

CLAIM `osinLemma94CaseOneSpurEnclosure : OsinLemma94CaseOneSpurEnclosureStatement` and `osinLemma94CaseOneRCellSpur_of_enclosedSucc`, GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellSpurEnclosureProof.lean

- Route: the walk-map separation of `IsNoncrossingClosedWalk` (`walkMap_facePerm_mem`, `walkMap_connected`, `not_faceClass_alpha`) uses only the chain and `turn_mem`. So a closed walk chained by first turns, bridges allowed, encloses `enclosedFaces` (the class of its non-bridge reversals off its edges) with the field `mem_iff` of `EnclosedFaceSet`. For Case 1: `turn_next` from the first-turn chain of 0484be5e5; f and Π off the enclosure, since one holds a walk dart and the first dart of p joins them off the walk; the two enclosures disjoint, since a chain in one never meets f or Π; so the exterior is off one of them.
- Both modules are written and wait for a probe. The MSI master has been absent since about 00:05 and the auth breaker is set.
