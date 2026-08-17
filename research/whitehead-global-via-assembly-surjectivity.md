---
rg: 2
id: whitehead-global-via-assembly-surjectivity
kind: route
title: Surjective degree-one assembly gives Whitehead vanishing
target: whitehead-vanishing-torsion-free
requires: [whitehead-is-degree-one-assembly-cokernel, degree-one-assembly-surjective-torsion-free]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Immediate: `Wh(G)` is the cokernel of `A_1^G`, and the cokernel of a
surjection is zero.

This is the route the literature actually walks.  Every known case of
`whitehead-vanishing-torsion-free` -- hyperbolic groups, finite-dimensional
CAT(0)-groups, lattices, 3-manifold groups, S-arithmetic groups -- arrives
this way, as the degree-one shadow of the `K`-theoretic Farrell--Jones
conjecture for that group.  It is recorded so that the root's decomposition
shows where progress has historically come from, next to the two routes this
repository's own material suggests, neither of which has ever produced a
case.
