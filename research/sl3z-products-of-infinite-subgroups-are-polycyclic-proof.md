---
rg: 2
id: sl3z-products-of-infinite-subgroups-are-polycyclic-proof
kind: route
title: Commuting infinite subgroups of SL_3(Z) centralize elements of infinite order
target: sl3z-products-of-infinite-subgroups-are-polycyclic
requires:
  - sl3z-infinite-order-centralizers-are-solvable
---

A periodic subgroup of `GL_3(Z)` is finite: its finitely generated subgroups
are finite (Burnside–Schur: finitely generated periodic linear groups in
characteristic zero are finite), finite subgroups of `GL_3(Z)` have bounded
order (Minkowski), and a directed union of finite groups of bounded order is
finite. So the infinite group `A` contains an element `a` of infinite order,
and `B <= C(a)` is solvable by `sl3z-infinite-order-centralizers-are-solvable`.
Symmetrically `A` is solvable. Since `[A, B] = 1`, `<A, B>` is a quotient of
`A x B`, hence solvable, and a solvable subgroup of `GL_3(Z)` is polycyclic
(Mal'cev). A group containing `F_2` is not solvable, which gives the listed
non-embeddings.
