---
rg: 2
id: map-groups-cannot-enter-the-rf-wreath-hierarchy
kind: claim
title: Minimally almost periodic groups have only trivial maps into the finite wreath hierarchy and its residual closure
distinct_from:
  recursive-wreath-libraries-have-stably-finite-group-algebras: that proves finiteness for the hierarchy and several limits; this identifies a representation-theoretic obstruction to using its finite stages as separating targets.
  binary-leavitt-unit-group-is-minimally-almost-periodic: that establishes rigidity of the specific Leavitt group; this propagates the resulting homomorphism obstruction through arbitrary finite wreath depth.
---

Let C_fin be the hierarchy defined in
`recursive-wreath-libraries-have-stably-finite-group-algebras`. If M is
minimally almost periodic, meaning every homomorphism M->U(d) is trivial,
then every homomorphism M->K with K in C_fin is trivial. The same holds
when K is residually C_fin.

In particular all maps from Q=L_(F_2)(1,2)^x into these targets are trivial.
The new finite marked-site methods therefore do not prove stable finiteness
of F_2[Q] by residual separation through this hierarchy. No claim that
F_2[Q] fails stable finiteness is made.

This obstruction does not automatically apply to arbitrary directed
colimits of C_fin groups. It does apply to increasing unions of such
groups when M is finitely generated, since the finite generating image
then lies in a single stage. The positive colimit finiteness theorem and
this narrower homomorphism obstruction must not be conflated.
