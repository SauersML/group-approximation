---
rg: 2
id: stw87-diagonal-order-zero-maps-annihilate-matrix-colours
kind: claim
title: Diagonal order-zero maps annihilate every noncommutative matrix colour
distinct_from:
  stw87-diagonal-expectation-order-zero-obstruction: that claim gives an exact one-half defect for a commutative two-point domain; this claim gives maximal defect one on every noncommutative matrix block and annihilates all such summands of an arbitrary finite-dimensional domain.
artifacts:
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
---

Let `X` be a set and let

```text
F = direct_sum_(j=1)^r M_(n_j).
```

Every c.p.c. order-zero map `theta:F->ell^infinity(X)` vanishes on each
summand `M_(n_j)` with `n_j>=2`.

Consequently, let `X` be a countable discrete metric space containing `n`
distinct points, where `n>=2`, let

```text
iota:M_n->C*_u(X)
```

be the associated finite matrix-corner inclusion, and let `E_X` be the
canonical diagonal expectation.  Then

```text
inf_theta norm(theta-E_X iota) = 1,                     (M)
```

where the infimum is over all c.p.c. order-zero maps
`theta:M_n->ell^infinity(X)` and the norm is the operator norm of a linear
map.  Thus postcomposition with the diagonal expectation loses every
noncommutative colour completely, at the maximal possible distance.
