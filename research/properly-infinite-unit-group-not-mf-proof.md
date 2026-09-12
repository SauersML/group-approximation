---
rg: 2
id: properly-infinite-unit-group-not-mf-proof
kind: route
title: The corner embedding carries a non-MF elementary group into the unit group
target: properly-infinite-unit-group-is-not-mf
requires:
  - full-idempotent-ring-has-properly-infinite-unit
  - full-complementary-idempotent-elementary-full-mf-radical
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
---

## Why sufficient

The hypothesis gives a properly infinite unit, so there are
`S_1,...,S_4,T_1,...,T_4` with `T_iS_j = delta_(ij)` and the corner map

```text
jmath(A) = 1 - p + sum_(i,j) S_iA_(ij)T_j,   p = sum_i S_iT_i,
```

is an injective homomorphism `GL_4(R) -> R^x`.

`EL_4(R)` is not MF: the prerequisite makes every homomorphism from it to an
MF group trivial, and `EL_4(R)` is nontrivial because `e_12(1) != 1` when
`R != 0`, which the fullness hypothesis forces.  A subgroup of an MF group
is MF, since MF groups are exactly the subgroups of unitary groups of norm
matrix coronas, so `R^x` cannot be MF once it contains an isomorphic copy of
`EL_4(R)`.

For `GL_n(R)`, the diagonal copy of `R^x` in the first coordinate is a
subgroup, so the same argument applies.
