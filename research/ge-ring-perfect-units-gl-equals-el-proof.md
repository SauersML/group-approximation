---
rg: 2
id: ge-ring-perfect-units-gl-equals-el-proof
kind: route
title: Commutators of units are elementary, so perfection absorbs the diagonal part
target: ge-ring-with-perfect-units-has-gl-equals-el
requires: []
artifacts:
  - research/artifacts/rank-one-headline-review-2026-09-07.md
---

## Proof

Conjugating `e_(ij)(r)` by `diag(a_1,...,a_n)` gives
`e_(ij)(a_i r a_j^(-1))`, so the diagonal subgroup normalizes `EL_n(R)`.

The Whitehead factorization puts `diag(a,a^(-1))` in `EL_2(R)` for every unit
`a`.  Since the diagonal normalizes `EL_2(R)`,

```text
[diag(a,a^(-1)), diag(b,1)]
  = diag(aba^(-1)b^(-1), a^(-1)a) = diag([a,b],1) in EL_2(R).
```

If `R^x` is perfect, every unit `c` is a product of commutators of units, so
`diag(c,1)` is a product of such elements and lies in `EL_2(R) <= EL_n(R)`.

An arbitrary invertible diagonal matrix reduces modulo `EL_n(R)` to
`diag(c,1,...,1)` with `c` the product of its entries, again by the Whitehead
factorization applied to consecutive pairs.  So the whole diagonal subgroup
lies in `EL_n(R)`.

The GE hypothesis writes any invertible matrix as a product of elementary
matrices and invertible diagonal matrices, and both factors now lie in
`EL_n(R)`.
