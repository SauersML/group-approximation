---
rg: 2
id: stw87-invariant-mean-retraction-has-coset-order-zero-gap
kind: claim
title: Invariant-mean retractions have an exact finite-coset order-zero gap
distinct_from:
  stw87-diagonal-expectation-order-zero-obstruction: that claim averages a two-point matrix corner onto the Roe diagonal; this claim averages Roe coefficients onto the reduced group algebra and works for every nontrivial finite coset partition.
artifacts:
  - research/artifacts/stw87-invariant-mean-retraction-audit-2026-08-30.md
---

Let `G` be a countable amenable group equipped with a proper left-invariant
bounded-geometry metric.  Every left-invariant mean `m` on
`ell^infinity(G)` induces, under the standard crossed-product identification,
a conditional expectation

```text
P_m:C*_u(G)=ell^infinity(G) crossed_product_r G -> C*_r(G)
```

which on the algebraic crossed product satisfies

```text
P_m(f u_g)=m(f) lambda_g.                              (1)
```

Suppose that `H<G` has finite index `k>=2`, and let
`phi:C^k->ell^infinity(G)` be the unital *-homomorphism whose minimal
projections are the characteristic functions of the left cosets of `H`.
Then

```text
inf_theta max_(1<=i<=k)
  norm(theta(e_i)-(P_m phi)(e_i)) = 1/k,               (2)
```

where the infimum is over all c.p.c. order-zero maps
`theta:C^k->C*_r(G)`.

Thus even though `P_m` is a conditional expectation and fixes the entire
reduced group algebra, postcomposing an order-zero colour with `P_m` can
have a rigid positive order-zero defect.  In particular, the invariant-mean
retraction for `G=Z^d` cannot by itself transfer nuclear-dimension colours
from `C*_u(Z^d)` to `C(T^d)`.
