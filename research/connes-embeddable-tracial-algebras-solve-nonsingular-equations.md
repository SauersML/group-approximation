---
rg: 2
id: connes-embeddable-tracial-algebras-solve-nonsingular-equations
kind: claim
title: Connes-embeddable tracial von Neumann algebras solve nonsingular unitary equations inside a matrix ultraproduct
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that is the group statement for hyperlinear coefficient groups, imported from Nitsche--Thom; this is the tracial-algebra statement with arbitrary unitary coefficients, from which the group case follows by taking the group von Neumann algebra.
  nonsingular-equations-preserve-matrix-certificates: that is the finite-dimensional root theorem consumed here; this passes it to every trace-preserving subalgebra of a matrix ultraproduct.
---

**Statement.**  Let `(M, tau)` be a tracial von Neumann algebra admitting a
unital trace-preserving `*`-embedding `j : M -> Q = prod_omega M_(d_n)`
into some tracial ultraproduct of matrix algebras.  Let `u_1, ..., u_k` be
unitaries of `M`, and let `w in F_k * <t>` have `deg_t(w) = m != 0`.  Then
there is `T in U(Q)` with

    w(j(u_1), ..., j(u_k), T) = 1 .

So `M` satisfies `tracial-algebras-solve-nonsingular-equations-in-extensions`
with `N = Q` and `iota = j`.

**Proof.**  Route `connes-embeddable-tracial-root-extension-proof`.  It uses
only the Gerstenhaber--Rothaus surjectivity recorded in
`nonsingular-equations-preserve-matrix-certificates` and two elementary
ultraproduct facts proved inline.

**Credit.**  No novelty is claimed.  This is Pestov's argument for hyperlinear
groups (as imported in `kervaire-laudenbach-holds-for-hyperlinear`), written
for tracial coefficients instead of group coefficients.
