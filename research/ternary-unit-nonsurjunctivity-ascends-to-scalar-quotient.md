---
rg: 2
id: ternary-unit-nonsurjunctivity-ascends-to-scalar-quotient
kind: route
title: A strict automaton on the ternary unit group is a strict automaton on its scalar quotient
target: projective-ternary-leavitt-group-nonsurjunctive
requires: [ternary-leavitt-unit-group-nonsurjunctive, leavitt-units-embed-in-their-scalar-quotient, surjunctivity-passes-to-subgroups]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

`L_(F_3)(1,2)^x` embeds in `PG = L_(F_3)(1,2)^x / {±1}` through the corner
homomorphism. Surjunctivity passes to subgroups, so a nonsurjunctive subgroup makes
`PG` nonsurjunctive. Concretely, the same memory and local rule define an automaton
over `PG` that acts on each left coset of the copy as the original automaton.
