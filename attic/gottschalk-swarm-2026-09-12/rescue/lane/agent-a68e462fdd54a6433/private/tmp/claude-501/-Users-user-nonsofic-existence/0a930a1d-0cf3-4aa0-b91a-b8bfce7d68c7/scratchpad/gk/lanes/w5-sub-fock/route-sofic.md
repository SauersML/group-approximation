---
rg: 2
id: sofic-subgroups-independent-cylinder-defects-proof
kind: route
title: Restrict a sofic approximation to the good free orbits of each finite subgroup and tensor the dihedral defects
target: sofic-subgroups-carry-independent-cylinder-defects
requires:
  - sofic-subgroups-carry-rank-models-violating-two-root-identity
  - finite-subgroup-data-cannot-force-defect-submultiplicativity
artifacts:
  - research/artifacts/fock-toeplitz-input-and-sofic-independence-2026-09-12.md
---

Artifact Section 2, Theorem 2.1.

1. **Model.** The permutation matrices of a sofic approximation `phi_i: H -> Sym(n_i)` give a homomorphism `sigma` into
   the unit group of the rank ultraproduct (`sofic-subgroups-carry-rank-models-violating-two-root-identity`).
2. **Freeness.** Fix a finite `K <= H`.
   * The union `W_i` of the `phi_i(K)`-orbits where the multiplication table of `K` holds and no nontrivial element has
     a fixed point is invariant, has `n_i - o(n_i)` points, and carries an honest free action.
   * So the permutation module is a free `F_2[K]`-module up to a part of dimension `o(n_i)`.
   * Left multiplication by `alpha` then has normalized rank `dim(alpha F_2[K]) / |K|`.
3. **Independence.** Frames on disjoint cylinders commute and meet trivially, because `s_A t_A s_B t_B = 0`. So
   `prod iota_(A_i)(D_8) ≅ D_8^k`, and its algebra is the tensor product of the factors.
   * The defect product is the tensor product of the `D_(A_i)`.
   * Images of tensor products of left multiplications multiply in dimension, and `dim(D F_2[D_8]) = 3`
     (route step 4 of `finite-subgroup-data-cannot-force-defect-submultiplicativity`). So the rank is `(3/8)^k`.
4. **No fixed vectors.**
   * For `g` of infinite order and any `N`, only `o(n_i)` points of `phi_i(g)` lie on cycles of length at most `N`.
     This is because `phi_i(g)^l` agrees with `phi_i(g^l)` off `o(n_i)` points, and `phi_i(g^l)` has `o(n_i)` fixed points.
   * The fixed space of a permutation over `F_2` has dimension equal to its number of cycles, which here is at most
     `n_i/N + o(n_i)`. So `rk Fix sigma(g) = 0`.
