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
