---
rg: 2
id: sl3z-infinite-order-centralizers-are-solvable
kind: claim
title: In SL_3(Z) the centralizer of every element of infinite order is solvable
---

Let `g in SL_3(Z)` have infinite order. Then its centralizer
`C(g) = {h in SL_3(Z) : hg = gh}` is solvable, hence polycyclic (Mal'cev:
solvable subgroups of `GL_n(Z)` are polycyclic). More precisely, `C(g)` is
abelian unless `g` is unipotent with `(g - 1)^2 = 0`; in that case `C(g)` is
conjugate, by an element of `GL_3(Q)`, into the upper triangular matrices.

The point for Serre's question is arithmetic: over `R` the element
`diag(l, l, l^-2)` with `l != ±1` has centralizer `GL_2(R)`, but a repeated
eigenvalue of an integral matrix of determinant one forces the eigenvalues to
be `1, 1, 1` or `-1, -1, 1`. Consequences are recorded in
`sl3z-products-of-infinite-subgroups-are-polycyclic`.
