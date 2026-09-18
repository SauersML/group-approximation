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

## Attempts

* **Resolved (w5-121): proved, via `kt-kernel-overgroups-polynomial-via-vertex-compressors-proof`.**
  The compressor is chosen after the column. For a column `u = he_i` of `h ∈ H` and a bad
  exponent `m` of `uv^T` with `m_(i0) < 0`, pick `P ∈ Mon` whose rows all lie in one open
  normal cone of `conv(∪ supp u_k)`, at a vertex `m*`, and all lie close to `e_(i0)`.
  Then `x^(−Pm*)·P·u` is `A`-unimodular: on the torus because `u` is `R`-unimodular, and on
  every coordinate hyperplane because only the `m*` monomial survives. By
  Quillen–Suslin and zero-entry extraction, `P·(uv^T) ∈ M_r(A)`. But `Pm` is negative in
  every coordinate, a contradiction. So every conjugated transvection is polynomial, and
  `H = SL_r(A)` by the transvection criterion. This uses one `P` per bad exponent, which
  avoids the cone gap `∩ P^(-1)(N^d) ⊋ N^d` of the fixed-shape compressors `I + kE_21`.
  It also treats the Koszul-type columns `(x_1,x_2,x_3)` like any other column. In `d = 1`,
  where `P = 1`, it reproves the maximality calibration.
