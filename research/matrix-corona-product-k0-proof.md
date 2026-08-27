---
rg: 2
id: matrix-corona-product-k0-proof
kind: route
title: Coordinatewise rank with a single stabilization bound
target: matrix-corona-product-k0-is-rank-bounded-sequences
requires: []
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Write `A = prod_n M_{d_n}` and `L(d) = { (z_n) : sup_n |z_n|/d_n < oo }`.

*`K_0`.*  A projection in `M_k(A) = prod_n M_{k d_n}` is a sequence `(p_n)`
of projections.  Two such are Murray--von Neumann equivalent in `M_k(A)`
exactly when their ranks agree coordinatewise: coordinatewise partial
isometries have norm one, so they assemble into an element of the bounded
product.  The rank sequences realizable at level `k` are exactly those with
`0 <= r_n <= k d_n`, and every such sequence is realized by coordinate
projections.  The projection monoid of `A` is therefore the union over `k` of
those sets -- **one `k` per element, not one per coordinate** -- which is the
set of nonnegative sequences with `sup r_n/d_n < oo`.  Its Grothendieck group
is `L(d)`.

*`K_1`.*  For a unitary `u = (u_n)` in `M_k(A)`, finite-dimensional
functional calculus writes `u_n = exp(i h_n)` with `h_n` self-adjoint and
`||h_n|| <= pi`.  The bound is uniform in `n`, so `h = (h_n)` lies in
`M_k(A)` and `t |-> exp(ith)` is a norm-continuous path from `1` to `u`.
Hence `K_1(A) = 0`.  (The same conclusion follows from `A` being a von
Neumann algebra, as `matrix-corona-k1-vanishes-proof` argues; the explicit
bound is given here because it is the same estimate that makes the `K_0`
computation's stabilization bound visible.)

## The correction

Taking `K_0(A) = prod_n Z` drops the requirement that a single stabilization
size serve every coordinate.  It fails already for `d_n = 1`, where `A` is
`ell^infinity` and `K_0(A)` is the bounded integer sequences: a projection in
`M_k(ell^infinity)` has rank at most `k` in every coordinate, so the sequence
`r_n = n` is not represented at any finite `k`.  Nothing in this graph
depended on the false direction of the inclusion `(+)_n Z <= L(d) <= prod_n Z`
-- only on injectivity of the left inclusion, which is unaffected -- so the
two nodes carrying the error keep their conclusions.
