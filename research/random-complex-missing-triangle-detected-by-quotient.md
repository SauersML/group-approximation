---
rg: 2
id: random-complex-missing-triangle-detected-by-quotient
kind: claim
title: A random missing triangle of a mid-range random complex survives in a finite quotient of its fundamental group
distinct_from:
  non-residually-finite-hyperbolic-group: that asks for some hyperbolic group that is not residually finite; this asks one specific random element of these random groups to be detected by a finite quotient, which residual finiteness of these groups would supply and which says nothing about other hyperbolic groups
  random-complex-group-no-large-finite-quotients: that says these groups have no large finite quotients at all, which together with Meshulam's theorem would refute the present claim
---

**OPEN.** For every `0 < η < 1/2`, with `p = n^(-1+η)`, sample `Y ~ Y(n,p)` and a
uniformly random missing triangle `Δ`. A.a.s. the perimeter of `Δ` survives in
some finite quotient of `π_1(Y)`.

* **Sufficient:** a.a.s. residual finiteness of `π_1(Y)`. The perimeter is a.a.s.
  nontrivial by `random-complex-mid-range-pair-properties`.
* **Constraint:** by `meshulam-random-complex-no-polynomial-quotients`, for every
  fixed `c`, a.a.s. every detecting quotient has order larger than `n^c`.
* **Kazhdan caution:** `π_1(Y)` has property (T) and is not cubulated, so the
  Wise--Agol virtual specialness that makes low-density random groups residually
  finite is unavailable.
