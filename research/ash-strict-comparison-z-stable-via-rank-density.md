---
rg: 2
id: ash-strict-comparison-z-stable-via-rank-density
kind: route
title: Rank density on ASH algebras gives purity from comparison and Z-stability from Winter
target: simple-unital-ash-strict-comparison-is-z-stable
requires: [simple-unital-ash-algebras-realize-ranks-approximately, rank-density-and-strict-comparison-give-purity]
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

Let `A` be a unital simple separable infinite-dimensional ASH algebra with
strict comparison.

1. `A` is nuclear.  Every subhomogeneous stage has traces, so `T(A)` is
   nonempty and `A` is stably finite.
2. The first prerequisite gives rank density, and the second turns rank
   density plus strict comparison into purity.
3. Every recursive subhomogeneous algebra over finite-dimensional compact
   metrizable spaces has finite nuclear dimension.  So `A` has locally finite
   nuclear dimension.
4. W. Winter, Invent. Math. 187 (2012), arXiv:1006.2731 (abstract read in
   lane `lix-toms-winter-2`): separable simple nonelementary unital
   (m, m-bar)-pure algebras with locally finite nuclear dimension absorb `Z`.
   With `m = m-bar = 0`, `A = A tensor Z`.

This is the same chain as `ah-strict-comparison-z-stable-via-rank-density`,
with the homogeneous rank-density input replaced by the open ASH input.
