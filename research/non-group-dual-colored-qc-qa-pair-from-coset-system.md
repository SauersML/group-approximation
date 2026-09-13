---
rg: 2
id: non-group-dual-colored-qc-qa-pair-from-coset-system
kind: route
title: A tracial non-R^U coset system with a nonabelian fibre image is a torsor digraph pair with non-group-dual symmetry
target: non-group-dual-colored-qc-qa-pair-exists
requires:
  - tracial-non-ru-coset-system-with-nonabelian-fibre-exists
  - coset-systems-are-torsor-isomorphism-games
---

Let `S` be a coset system with a tracial state, no unital *-homomorphism
`A(S) -> R^U`, and some fibre image `L_q` nonabelian.  Take `X = X(S_1)` and
`Y = X(S)`, the torsor digraphs of the homogeneous and twisted systems.

- **The gap.**  By (T1) of `coset-systems-are-torsor-isomorphism-games`,
  `A(Iso(X,Y)) ≅ A(S)`.  So `X ≅_qc Y`, and `X, Y` are not `qa`-isomorphic.
- **Not a group dual.**  By (T3) and (T4), `Qut(X ⊔ Y)` with the cross colour
  has `Qut X(S_1)` as a Hopf quotient.  That quotient is not cocommutative,
  since `L_q` is nonabelian.  So `Qut(X ⊔ Y)` is not a group dual.
