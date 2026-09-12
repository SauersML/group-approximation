---
rg: 2
id: homogeneous-tower-k1-failure-needs-twice-rank-dimension
kind: claim
title: A homogeneous tower that fails K1-injectivity has a block of dimension at least twice its rank at every late stage
distinct_from:
  bundle-endomorphism-unitaries-stable-range: that is the single-stage stable range lemma; this passes it through an inductive limit to constrain every presentation of a non-K1-injective limit.
  untwisted-point-evaluations-kill-k1-obstructions: that constrains the connecting maps; this constrains the dimensions of the building blocks.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Let `A = lim (A_j, phi_j)` with unital injective connecting maps and

```text
A_j = direct-sum_(k=1..n_j) Gamma(X_(j,k), End E_(j,k)),
```

where each `X_(j,k)` is a finite CW complex of dimension `d_(j,k)` and
`E_(j,k)` has constant positive rank `r_(j,k)`. If for infinitely many `j`
every block satisfies `d_(j,k) + 1 <= 2 r_(j,k)`, then `A` is K1-injective.

Equivalently, if `A` is not K1-injective, then for all sufficiently large `j`
some block of `A_j` has `d_(j,k) >= 2 r_(j,k)`.
