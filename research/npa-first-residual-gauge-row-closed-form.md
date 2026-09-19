---
rg: 2
id: npa-first-residual-gauge-row-closed-form
kind: claim
title: The trailing-zero pair row is the first residual gauge condition in closed form at every level
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Let `r_j` denote the alternating word of length `j` ending in `1`, and for a
level-`k` basis word `p` with a trailing `0` in some party let
`T_p = e_p - e_[reduce(p)]` be its trailing-zero relation.  For every `k >= 4`
the pairing of two such relations,

```text
A_k := < T_[((0), r_(k-2))] ,  Gamma_k(y)  T_[((0), r_(k-1))] >,
```

is the level-`k` row

```text
A_k = 2 y_[(empty, r_(2k-3))] - 2 y_[((0), r_(2k-3))],
```

supported entirely on moment classes of degree `2k-3`, hence on classes already
present at level `k-1`.

This is exactly twice the left-hand side of the first of the two residual
conditions of the germ step, which the source obtained only for the transitions
`2->3`, `3->4`, `4->5`.  So the first residual row is now available in closed
form, uniformly in `k`.

The companion row `B_k`, built from two dressings `D_[(empty, e_(k-3))]` and
`D_[(empty, e_(k-2))]`, is claimed by the same source to carry the signature
`y_[(empty,m)] - y_[((1),m)]` of the second residual condition.  That signature
is consistent with the germ step, but the full six-term identity is not asserted
here.
