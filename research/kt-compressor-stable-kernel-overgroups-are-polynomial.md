---
rg: 2
id: kt-compressor-stable-kernel-overgroups-are-polynomial
kind: claim
title: A Mon-stable subgroup of SL_r(Laurent) containing SL_r(polynomial) with polynomial root contents has polynomial entries
distinct_from:
  kt-compressor-stable-polynomial-content-overgroups-are-gamma: that allows elements with nontrivial SL_d(Z) projection; this is the kernel case, which is equivalent to it by kt-compressor-sandwich-equivalent-to-kernel-polynomiality
  kt-compressor-stable-overgroups-have-polynomial-content: that controls the root subgroups; this asks for control of all entries
---

**OPEN.** Let `A = F_q[x_1,…,x_d] ⊂ R = F_q[x_1^(±1),…,x_d^(±1)]`, `r,d ≥ 3`, and
`Mon = SL_d(Z) ∩ M_d(N)` acting on `R` by `x^v ↦ x^(Pv)` and entrywise on matrices. Let
`H ≤ SL_r(R)` with

```text
SL_r(A) ≤ H,     P·H ≤ H for all P ∈ Mon,     H ∩ U_12(R) = U_12(A).
```

Then `H = SL_r(A)`.

By `kt-compressor-sandwich-equivalent-to-kernel-polynomiality` this is equivalent to
`kt-compressor-stable-polynomial-content-overgroups-are-gamma`, and so it closes the route
`kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich`.

## What is known

* **(Dichotomy.)** The `A`-span of the entries of `H` is `A` or `R`, so a counterexample
  has entries spanning all of `R` while every root element stays polynomial.
* **(One variable.)** For `d = 1` the analogue holds with no stability hypothesis:
  `SL_r(F_q[t])` is a maximal subgroup of `SL_r(F_q[t^(±1)])`, by density in
  `SL_r(F_q((t)))`.
* **(Dead candidates.)** Lattice and semilinear lattice stabilizers give nothing new. An
  `SL_r(A)`-stable `A`-submodule of `R^r` is `I^r`, its stabilizer is `SL_r(O(I))`, and
  the root content of that is the multiplier ring `O(I)`. Row-type unipotents
  `I + e_k u^T` with a non-polynomial entry have a non-polynomial root element after one
  commutator with `e_(mn)(1)`. Monomial and torus elements with nonconstant entries
  conjugate `U_ij(A)` outside `A`.

## Where a proof must use the compressors

For `d ≥ 2` no valuation ring meets `R` in `A`, so the one-variable density argument only
gives `H·SL_r(R ∩ O_ν) = SL_r(R)` for the valuations `ν` that `H` moves. Transvections
`h e_ij(a) h^(-1) = I + a·(he_i)(e_j^T h^(-1))` lie in `H`. Splitting them into elementary
matrices needs coefficients in `R`, which `H` does not contain.
