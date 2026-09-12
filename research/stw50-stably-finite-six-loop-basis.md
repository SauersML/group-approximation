---
rg: 2
id: stw50-stably-finite-six-loop-basis
kind: claim
title: Construct six explicit generators in Aut of the stably finite irrational rotation algebra
root: true
distinct_from:
  stw99-problem-l-explicit-automorphism-loops: The original problem permits the Kirchberg alternative; this retained target requires loops inside the stably finite rotation algebra itself.
  stw50-explicit-basis-of-rotation-retraction-kernel: That kernel target permits the Kirchberg counterpart and asks for four complementary loops; this target fixes A_theta and asks for a full six-loop basis.
artifacts:
  - research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md
---

For an irrational theta, construct six explicit based point-norm
continuous automorphism loops on A_theta itself whose homotopy
classes form a Z-basis of pi_1(Aut(A_theta),id).

This is the stably finite alternative of STW Problem L, retained
as an open target after the graph-model construction for the
Kirchberg alternative. The latter's fixed classification
isomorphisms cannot transport loops into A_theta, which is
stably finite. An abstract weak homotopy equivalence with the
O_infinity tensor counterpart does not produce explicit preimages.

## Attempts

The two canonical rotation loops already split off Z^2. The
Kirchberg graph tensor model constructs the other four homotopy
directions after O_infinity absorption, but its graph generators
are properly infinite partial isometries and do not give a model
of the finite algebra. Transporting them back requires actual
point-norm continuous loops on A_theta, not an abstract inverse
on homotopy groups. That is the unfilled step.
