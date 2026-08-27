---
rg: 2
id: zariski-envelope-compression-rigidity-proof
kind: route
title: Instantiate the chain-condition principle on Zariski-closed subgroups
target: zariski-envelope-compression-rigidity
requires: [noetherian-invariant-compression-rigidity]
artifacts:
  - GroupApproximation/Algebra/ZariskiEnvelopeEndpoint.lean
  - GroupApproximation/Algebra/ZariskiClosedSubgroup.lean
  - GroupApproximation/Algebra/ZariskiDescendingChain.lean
  - GroupApproximation/Criterion/ClosedEnvelopeCompressionCore.lean
---

## Why sufficient

Take `P` to be the poset of Zariski-closed subgroups of `GL(V)` under
inclusion, with `H` acting through `rho` by conjugation — conjugation by a
fixed invertible matrix is a homeomorphism of the Zariski topology and a
group automorphism, so it is an order-automorphism of `P`.  Set
`I(L) = closure_Z(rho(L))`.

- **Monotone:** larger subgroup, larger closure.
- **Equivariant:** `closure_Z(rho(h) X rho(h)^{-1}) =
  rho(h) closure_Z(X) rho(h)^{-1}` since conjugation is a Zariski
  homeomorphism; applied to `X = rho(L)` this is
  `I(h L h^{-1}) = rho(h) I(L) rho(h)^{-1}`.
- **Descending chain condition:** in a strictly descending chain of closed
  subgroups of `GL(V)`, each proper closed inclusion strictly drops the
  pair (dimension, number of irreducible components) lexicographically —
  a proper closed subgroup of an algebraic group has smaller dimension or
  the same dimension and strictly fewer components — and that pair takes
  values in a well-ordered set, so the chain terminates.

`noetherian-invariant-compression-rigidity` then gives
`rho(s) closure_Z(rho(L)) rho(s)^{-1} = closure_Z(rho(L))`, and the left
side is `closure_Z(rho(s L s^{-1}))` by equivariance.
