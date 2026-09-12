---
rg: 2
id: random-complex-large-quotients-split-at-exp-pn
kind: route
title: Split the large-quotient premise at exp(n^eta/8) into the proved first-moment regime and the open superexponential regime
target: random-complex-group-no-large-finite-quotients
requires: [random-complex-group-no-quotients-below-exp-pn, random-complex-group-no-quotients-above-exp-pn]
---

## Why sufficient

Fix `η` from `random-complex-group-no-quotients-above-exp-pn`, any `c > 0`, and
`p = n^(-1+η)`.

- `pn - 24 log n = n^η - 24 log n -> infinity`, so
  `random-complex-group-no-quotients-below-exp-pn` applies. A.a.s. there is no
  nontrivial finite quotient of order at most `exp(n^η/8)`.
- The open claim excludes a.a.s. every order above `exp(n^η/8)`.
- So a.a.s. `π_1(Y(n,p))` has no nontrivial finite quotient at all, in particular
  none of order greater than `n^c`.

The conclusion is stronger than the premise. The routes that consume the premise
together with `meshulam-random-complex-no-polynomial-quotients` are unchanged.
The point of this route is that the only open input is now the regime above
`exp(n^η/8)`, not everything above `n^c`.
