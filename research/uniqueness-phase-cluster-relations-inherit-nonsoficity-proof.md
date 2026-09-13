---
rg: 2
id: uniqueness-phase-cluster-relations-inherit-nonsoficity-proof
kind: route
title: Identify the uniqueness-phase cluster relation with a compression of the orbit relation
target: uniqueness-phase-cluster-relations-inherit-nonsoficity
requires:
  - fpbs-cluster-count-trichotomy
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
---

Full proof in Sections 0--2 of the artifact.

- **Freeness and ergodicity** (Section 0). For `g != 1` some edge is moved. Nonatomic coordinates give
  `mu{xi(e) = xi(g^-1 e)} = 0`. Edge stabilizers have order at most two, so orbits on `E` are infinite and
  the shift is mixing.
- **Equality** (Theorem 2.1). If `xi` and `g^-1 . xi` lie in `A_p`, then `1` and `g` lie in infinite
  clusters of `omega_p(xi)`. For `p > p_u`, `fpbs-cluster-count-trichotomy` gives a unique infinite cluster
  a.s., so they lie in the same one. For `p = 1` all edges are open.
- **Permanence** (Lemmas 1.2--1.4, proved from the operator-algebraic definition stated in the artifact,
  the relation analogue of Păunescu's Definition 1.4).
  - Restriction to a positive-measure set preserves soficity: take the corner by `Theta(1_A)` and correct
    the commuting permutations on `o(n)` points.
  - Amplification of an ergodic relation from `A` preserves soficity: use the matrix picture
    `L(R) ≅ p M_m(L(R|_A)) p` given by partial isomorphisms into `A`. Full group elements become matrices
    of partial permutations.
  - A sofic orbit relation of a free action makes the group sofic, because
    `tau(u_g) = mu(Fix g) = 0` for `g != 1`.
- **Conclusion.** If `R_p` is sofic, then `R_p|_(A_p) = R_G|_(A_p)` is sofic, so `R_G` is sofic, so `G` is
  sofic. The hyperlinear version replaces permutation ultraproducts by `R^omega` throughout.
