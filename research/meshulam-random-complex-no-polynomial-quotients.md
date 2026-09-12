---
rg: 2
id: meshulam-random-complex-no-polynomial-quotients
kind: claim
title: Mid-range random complex groups have no nontrivial quotient of polynomial order
distinct_from:
  random-complex-mid-range-pair-properties: that collects nontriviality, hyperbolicity and local expansion; this excludes small finite quotients, a statement about the profinite side that those properties do not touch
---

**ESTABLISHED (literature import).** R. Meshulam, *Bounded quotients of the
fundamental group of a random 2-complex*, arXiv:1308.3769 (17 Aug 2013),
abstract, read from arXiv on 2026-09-11:

> For a fixed `c>0` it is shown that if `p = (6+7c) log n / n` then a.a.s. the
> fundamental group `π(Y)` does not have a nontrivial quotient of order at most
> `n^c`.

**Mid-range form.** Adding triangles adds relators, so a finite quotient of
`π_1(Z)` for `Z ⊇ Y` is a finite quotient of `π_1(Y)`. The property "no
nontrivial quotient of order at most `n^c`" is therefore increasing, and it
survives the standard monotone coupling. So for every `0<η<1/2` and every fixed
`c > 0`, a.a.s. `π_1(Y(n, n^(-1+η)))` has no nontrivial quotient of order at
most `n^c`.

This does not exclude quotients of superpolynomial order. Those are what
`random-complex-missing-triangle-detected-by-quotient` would need, and what
`random-complex-group-no-large-finite-quotients` would forbid.

CITATION
meshulam-random-complex-no-polynomial-quotients-citation
