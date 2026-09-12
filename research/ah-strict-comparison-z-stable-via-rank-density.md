---
rg: 2
id: ah-strict-comparison-z-stable-via-rank-density
kind: route
title: Rank density from Brown--Perera--Toms, purity from comparison, Z-stability from Winter
target: simple-ah-strict-comparison-is-z-stable
requires: [ah-algebras-realize-ranks-approximately, rank-density-and-strict-comparison-give-purity]
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

A second route into the AH cell of Toms--Winter, independent of Toms's
almost-divisibility note arXiv:1102.0932 used by
`simple-ah-strict-comparison-z-stable-citation`.

Let `A` be a unital simple separable infinite-dimensional AH algebra with
strict comparison.

1. `A` is nuclear, and `T(A)` is nonempty, being an inverse limit of nonempty
   compact convex sets.  So `A` is exact and stably finite.
2. The first prerequisite gives rank density.  The second turns rank density
   plus strict comparison into purity.
3. AH algebras have locally finite nuclear dimension.  Each summand
   `p(C(X) tensor M_N)p` is approximated by images of summands over finite
   polyhedra with inverse limit `X`, and such images have finite nuclear
   dimension.
4. W. Winter, *Nuclear dimension and Z-stability of pure C*-algebras*, Invent.
   Math. 187 (2012), arXiv:1006.2731 (abstract read in this lane): separable
   simple nonelementary unital (m, m-bar)-pure algebras with locally finite
   nuclear dimension absorb `Z`.  Purity is the case `m = m-bar = 0`, so
   `A = A tensor Z`.

The AH hypothesis is used twice: for rank density (building blocks with
trivial rank-one projections) and for locally finite nuclear dimension.  Any
class with both properties gets the same conclusion, which is why ASH
algebras, with locally finite nuclear dimension but unknown rank density, are
the next case.
