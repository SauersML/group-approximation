---
rg: 2
id: finite-packet-holonomy-fixed-simplex-proof
kind: route
title: Transport from a base vertex and impose path independence around cycles
target: finite-packet-holonomy-cuts-the-multiplicity-simplex
requires:
  - finite-packet-rank-polytope-is-complete
artifacts:
  - research/artifacts/property-t-free-rank-polytope-holonomy-integration-2026-08-25.md
---

Fix a path from the base vertex to every vertex.  Equation `(HRS1)` transports
one base state along these paths and determines every `p_v`.  Two paths give
the same transported state exactly when their resulting cycle permutation
fixes the base state.  Thus path-independent network states are precisely
the points of `Delta^H`, proving `(HRS2)` and the stated bijection.

Each selector rank is affine in the local multiplicities.  Composing with
the chosen path permutation makes it affine in the base state.  Collecting
the finitely many reads gives `L`, so `(HRS3)` follows from the rank-polytope
theorem.

An `H`-fixed vector is constant on every `H`-orbit.  Assigning nonnegative
total masses to the `t` orbits with sum one identifies the fixed set with a
`(t-1)`-simplex.  For one orbit all `s` coordinates are equal, and their sum
is one, proving `(HRS4)`.  Substitution in the affine rank read gives
`q_bar`; the projection-trace inequality `(RPP3)` gives `(HRS5)`.
