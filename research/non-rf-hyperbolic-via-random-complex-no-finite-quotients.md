---
rg: 2
id: non-rf-hyperbolic-via-random-complex-no-finite-quotients
kind: route
title: A mid-range random complex group with no finite quotients is a non-residually-finite hyperbolic group
target: non-residually-finite-hyperbolic-group
requires: [random-complex-mid-range-pair-properties, meshulam-random-complex-no-polynomial-quotients, random-complex-group-no-large-finite-quotients]
---

## Why sufficient

Fix `η` and `c` from the open premise.

* A.a.s. `π_1(Y)` is hyperbolic and nontrivial.
* Meshulam excludes nontrivial quotients of order at most `n^c`; the premise
  excludes larger ones.
* So some sample has a nontrivial hyperbolic `π_1(Y)` with no nontrivial finite
  quotient, which is not residually finite.

The split is genuine. Meshulam's counting does real work below polynomial
order, and the premise is only the large-quotient regime.
