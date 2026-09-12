---
rg: 2
id: random-complex-group-no-quotients-below-exp-pn
kind: claim
title: Linial--Meshulam groups with pn >> log n have no nontrivial finite quotient of order at most exp(pn/8)
distinct_from:
  meshulam-random-complex-no-polynomial-quotients: that imports Meshulam's Theorem 1.3, order at most n^c at p = (6+7c) log n / n; this runs the same first-moment argument at general p, where the order bound becomes exp(pn/8), superpolynomial in the mid range.
  random-complex-group-no-large-finite-quotients: that is the open premise excluding every quotient of order above n^c; this proves the premise for orders up to exp(pn/8), so what stays open there is exactly the orders above exp(n^eta/8).
---

**ESTABLISHED.** Let `Y ~ Y(n,p)` be the Linial--Meshulam complex: complete
1-skeleton on `n` vertices, each triangle present independently with
probability `p`. Suppose

```text
pn - 24 log n -> infinity.
```

Then a.a.s. `π_1(Y)` has no nontrivial finite quotient of order at most
`exp(pn/8)`.

**Mid range.** For `p = n^(-1+η)` with `0 < η < 1`, the bound is
`exp(n^η/8)`, which eventually exceeds every `n^c`. So in the regime of
`random-complex-mid-range-pair-properties`, Meshulam's polynomial bound
`meshulam-random-complex-no-polynomial-quotients` improves to a stretched
exponential one, by Meshulam's own argument.

Derivation: `random-complex-no-quotients-below-exp-pn-proof`.

## What it changes

- The open premise `random-complex-group-no-large-finite-quotients` is only
  open for orders above `exp(n^η/8)`. That remaining regime is recorded as
  `random-complex-group-no-quotients-above-exp-pn`.
- The first moment cannot go further by itself. It pays `|G|` per support edge
  against `e^(-pn/3)` per edge, so it stops at order about `exp(pn/3)`.
  Beyond that, a proof has to use the forced label equalities on present
  triangles, or global structure of the random complex.
