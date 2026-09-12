---
rg: 2
id: el3-unit-root-matrix-units-iff-two-root-identities
kind: claim
title: The unit root elements of an EL_3 model act by matrix units exactly when N_12 squares to zero and N_23 N_12 = 0
distinct_from:
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that assumes the matrix-unit hypothesis and proves triviality for simple non-directly-finite coefficient rings in characteristic two; this characterizes the matrix-unit hypothesis itself by two product identities, for any rings, in any characteristic.
  block-unipotent-rank-models-of-leavitt-el3-are-trivial: that kills models whose root subgroups act by block-supported additive maps; this is an exact algebraic criterion on the six unit root unipotents, with the idempotents constructed rather than assumed.
  free-rank-models-on-sl3-admit-no-block-support: that uses the easy direction (block support forces N_23 N_12 = 0) to exclude block support on free content; this proves the converse, that N_12^2 = 0 and N_23 N_12 = 0 already construct the orthogonal idempotents and matrix units.
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Let `R` and `M` be unital rings and `sigma : EL_3(R) -> M^x` a homomorphism, and put
`N_ab = sigma(x_ab(1)) - 1` for roots `a != b` in `{1,2,3}`. The following are equivalent:

1. There are pairwise orthogonal idempotents `p_1, p_2, p_3` in `M` with
   `sigma(x_ij(1)) = 1 + u_ij`, `u_ij` in `p_i M p_j`, `u_ij u_jk = u_ik` and `u_ij u_ji = p_i`
   for distinct `i, j, k`. This is the hypothesis of
   `matrix-unit-root-rank-models-of-simple-el3-are-trivial` and its odd-characteristic
   companion.
2. `N_ab N_cd = 0` whenever `b != c`.
3. `N_12^2 = 0` and `N_23 N_12 = 0`.

The idempotents are forced: `p_i = N_ij N_ji`. In characteristic two the first identity in 3
is automatic, so a single identity decides.

Proof: `research/artifacts/el3-two-root-identities-2026-09-12.md`, Section 1. The same-row and
same-column products, such as `N_12 N_13` and `N_12 N_32`, then vanish as a consequence.
