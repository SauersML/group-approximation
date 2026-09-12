---
rg: 2
id: stably-finite-group-ring-with-non-mf-elementary-groups-proof
kind: route
title: Embed the perfect unit group in two elementary coordinates and use the faithful trace for stable finiteness
target: stably-finite-group-ring-with-non-mf-elementary-groups
requires:
  - binary-leavitt-all-ranks-full-mf-radical
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
---

## Why sufficient

**Perfect units sit in two elementary coordinates.**  Let `R` be any
unital ring and `a, b in R^x`.  Put

```text
w(a) = e_12(a) e_21(-a^-1) e_12(a) = [[0, a], [-a^-1, 0]],
D(a) = w(a) w(-1) = diag(a, a^-1) in EL_2(R).                          (1)
```

The matrix `d(b) = diag(b, 1)` normalizes `EL_2(R)`, since
`d(b) e_12(r) d(b)^-1 = e_12(br)` and `d(b) e_21(r) d(b)^-1 = e_21(r b^-1)`.
Hence

```text
[D(a), d(b)] = diag([a,b], 1) in EL_2(R),                               (2)
```

because `D(a) in EL_2(R)` and `d(b) D(a)^-1 d(b)^-1 in EL_2(R)`.  Finite
products give `diag([R^x, R^x], 1) <= EL_2(R)`.  Nothing assumes `d(b)`
elementary or `EL_2(R)` normal in `GL_2(R)`.

**The embedding.**  By the second prerequisite `H` is perfect, so every
`h in H` is a product of commutators of elements of `H <= Z[H]^x`, and by
(2) `diag(h, 1) in EL_2(Z[H])`.  The map `h |-> diag(h,1)` is an injective
homomorphism `H -> EL_2(Z[H])`, and stabilizing, `H -> EL_n(Z[H])` for
every `n >= 2`.

**Non-MF.**  By the first prerequisite `H` is not MF.  A norm-matrix-corona
embedding of a group restricts to an embedding of every subgroup, so MF
passes to subgroups and `EL_n(Z[H])` is not MF.

**Stable finiteness.**  The left regular representation embeds `Z[H]` in
`C[H] <= C*_r(H)` (apply a group-ring element to `delta_1` to see
faithfulness).  The canonical trace `tau` on `C*_r(H)`, and its matrix
amplifications, are faithful: if `T >= 0` and `tau(T) = 0` then
`T^(1/2) delta_1 = 0`, and since `T^(1/2)` commutes with right
translations `T^(1/2) delta_h = 0` for all `h`, so `T = 0`.  If `AB = I`
in `M_m(C*_r(H))`, then `B` is bounded below, `B*B` is invertible,
`v = B (B*B)^(-1/2)` is an isometry, and `tau(I - v v*) = tau(I) - tau(v* v)
= 0` forces `v v* = I`; so `B` is invertible and `BA = I`.  This is
Kaplansky's theorem (Fields and Rings, 1969, Chapter 2, Problem 23) and
holds in every matrix size, so the subring `Z[H]` is stably finite.

**Finite generation and countability.**  A finite generating set of `H`
with inverses generates `Z[H]` as a unital ring, and `H` is countable.
