---
rg: 2
id: arithmetic-universal-fd-null-witness-proof
kind: route
title: Filter the lattice complement and kill its invariant sector by co-density
target: arithmetic-leak-has-fd-null-laplacian-witness
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

The positive Laplacian `Delta_C` is bounded by `L=4|S|`.  Property `(T)`
bounds it below by `kappa>0` off the `C`-invariant vectors, so `x_N` contracts
there by `q^N`.  Exact finite-dimensional co-density identifies the
`C`-invariant and `A`-invariant sectors; hence `h-1` vanishes on the other
summand and `(APW2)` follows.

For a projectively `C`-central unitary, pass twice to the adjoint action.
The selected full-rank operator `T=Ad U` is then literally `C`-fixed.
Evaluating `y_N` leaves the `h` displacement of `T`; the normalized trace of
an adjoint unitary is the squared modulus of the underlying normalized
trace, which gives `(APW3)`.
