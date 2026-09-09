---
rg: 2
id: affine-finitary-linear-radical-proof
kind: route
title: Identify the coset action with lattice cosets, show the action is faithful, and read off both subgroups
target: affine-finitary-linear-radical-is-the-whole-kernel
requires:
  - ascending-hnn-finitary-linear-family-is-sofic-non-mf
  - affine-semidirect-sl3-source-has-property-t
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

The second prerequisite supplies property (T) of `L = Z^3 x| SL_3(Z)`,
which is finitely generated; `alpha(b,A) = (mb,A)` is injective with
image `m Z^3 x| SL_3(Z)` of index `m^3 > 1`. So the first
prerequisite applies and gives a finitely generated sofic non-MF group
with no nontrivial finite normal subgroup, together with both
inverse-image identities over the faithful quotient.

It remains to identify that quotient. The ascending HNN extension is
`V = Z[1/m]^3 x| (SL_3(Z) x Z)`, with `u` acting by dilation by
`m`, faithfully represented by the affine matrices
`[[m^k A, b],[0,1]]` because the upper-left determinant determines
`k`. Identify `gL` with the lattice `g Z^3`; the stabilizer of
`Z^3` is exactly `L`, since `m^k A Z^3 + b = Z^3` forces `k = 0`
and `b in Z^3`. The kernel `B` of this action is trivial: an element
fixing every `v + m^j Z^3` has scale zero, and then `(A-I)v + b` lies
in the intersection of the `m^j Z^3` for all `v`, which is zero, so
`A = I` and `b = 0`. Hence `Q = V`.

`V` is residually finite by reduction modulo primes not dividing `m`,
which separates the displayed affine matrices. So `D_V(L) = 1` and
`Rad_MF(V) = 1`, and both inverse images collapse to the kernel
`GL_fin(F_2^(X))`, which the permanence claim identifies as infinite,
locally finite and simple.
