---
rg: 2
id: unitriangular-data-cannot-assemble-corner-leavitt-families
kind: claim
title: The unitriangular group has a regular rank model with nonzero two-root defect, so positive-root data never force the identity or assemble a corner Leavitt family
distinct_from:
  sofic-subgroups-carry-rank-models-violating-two-root-identity: that turns a sofic approximation of a sofic subgroup into a model free on one D_8; this realizes the free profile on every finite subgroup of the unitriangular group at once, compatibly with every rank equality from conjugation, and applies it to the Heisenberg centre pairing and to the rank-four Cuntz assembly.
  finite-positive-root-fragments-have-marked-regular-models: that gives finite regular models of finite positive-root fragments of the affine-Leavitt Steinberg presentation; this is one direct-limit model of the whole unitriangular group, used against the two-root gate and the corner Leavitt family.
  heisenberg-centre-pairing-constrains-two-root-defect: that asserts the centre pairing forces the two-root defect to vanish; this exhibits a model satisfying every input of that mechanism with rk(N_23 N_12) = 3/8.
  rank-four-isometry-relations-give-corner-cuntz-family: that asserts a corner Leavitt family from a nonzero defect in rank models of R^x; this shows no derivation from positive-root data alone can produce it.
  unipotent-frame-relations-cannot-assemble-corner-cuntz-family: that uses the p^2-dimensional translation model through the superdiagonal entries, where N_13 = N_14 = 0, so it covers derivations from relations of U_4(R) only; this uses the regular model with the free profile on every finite subgroup, so it also covers rank equalities across root positions from Weyl conjugation and the weakened endpoint T_0 S_0 = e = T_1 S_1, T_1 S_0 = 0, rk(T_1) > 0.
artifacts:
  - research/artifacts/heisenberg-and-rank-four-positive-root-firewall-2026-09-12.md
---

**ESTABLISHED** (proof route `unitriangular-data-corner-leavitt-firewall-proof`; artifact
Sections 1 and 3).

Let `K` be a field of characteristic `p`, `R` a countable `K`-algebra such as `L_K(1,2)` with `K`
finite, `n >= 3`, and `L` a countable locally finite group, for example `UT_n(R)` or
`UT_3(R) ⋊ <diag(w,w,w)>` with `w = s_0 t_1 + s_1 t_0`. Then:

1. `UT_n(R)` is locally finite.
2. The direct-limit regular representation is a homomorphism `sigma_reg : L -> M^x` into a rank
   ultraproduct over `F_p` with `rk(sigma_reg(alpha)) = rank(lambda_Q(alpha)) / |Q|` for every finite
   `Q <= L` and `alpha` in `F_p[Q]`. These ranks are invariant under every isomorphism of finite
   subgroups, conjugation by `GL_n(R)` included.
3. `rk((sigma_reg(x_23(1)) - 1)(sigma_reg(x_12(1)) - 1)) = 3/8` for `p = 2`, and it is at least `p^-3`
   for odd `p`.

**Consequences.**

* **The centre pairing dies as a mechanism.** The Steinberg relations of `UT_3(R)` with any
  coefficients, centrality of `n_13(R)`, the pairing `n_13(ab)`, rank values across positions, the
  branch split over `e_i = s_i t_i` and the swap `diag(w,w,w)` all hold in `sigma_reg`, where
  `rk(N_23 N_12) = 3/8`. The `2^k` depth-`k` branch products each have rank `3/8`, so no orthogonal
  chain appears.
* **Positive-root data cannot assemble a corner Leavitt family.** Suppose a derivation forms `e, S_i, T_j`
  by ring operations from `sigma(UT_4(R))`, and proves `T_i S_j = delta_ij e`,
  `S_0 T_0 + S_1 T_1 = e` and `rk(e) = rk(N_23 N_12)` from relations of `UT_4(R)`, the ring structure of
  `M`, and conjugation-invariant ranks. Applied to `sigma_reg`, it would give idempotents with
  `rk(e) >= 2 rk(e) > 0`. The same holds for the weakened endpoint `T_0 S_0 = e = T_1 S_1`,
  `T_1 S_0 = 0`, `rk(T_1) > 0`: then `S_0 T_0 (e - S_1 T_1)` and `S_1 T_1` are orthogonal idempotents in
  `eMe`, each of rank at least `rk(e)` (artifact, Remark after Theorem 2). So the four-index assembly
  needs `sigma` as an operator on negative root elements or torus units, jointly on a nonsofic subgroup.

The conclusion `N_23 N_12 = 0` for rank models of `EL_3(R)` is not affected: it is the open gate
`rank-models-of-el3-satisfy-the-two-root-identities`.

## Attempts

Established by direct construction (lane `w4-heisenberg`, 2026-09-12). The theorem is elementary.
Its content is the application: it closes the centre-pairing plan of
`heisenberg-centre-pairing-constrains-two-root-defect` and the positive-root form of checks (a)-(c)
of `rank-four-isometry-relations-give-corner-cuntz-family`.
