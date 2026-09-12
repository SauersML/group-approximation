---
rg: 2
id: unipotent-frame-relations-cannot-assemble-corner-cuntz-family
kind: claim
title: The unitriangular EL_4 frame has a rank model with nonzero two-root defect and no corner Cuntz family
distinct_from:
  rank-four-isometry-relations-give-corner-cuntz-family: that asserts a nonzero defect assembles a corner Leavitt family; this shows every relation it lists holds in a model of the unitriangular group with nonzero defect where no such family exists, so a proof of it must use sigma outside that group.
  sofic-subgroups-carry-rank-models-violating-two-root-identity: that turns sofic approximations of a sofic subgroup containing D_8 into characteristic-two rank models; this gives an explicit p^2-dimensional model of U_4(R) in every characteristic, applies it to the four-index frame, and shows the corner-family conclusion fails there.
  heisenberg-centre-pairing-constrains-two-root-defect: that is the centre-pairing plan; the same model restricted to U_3(R) has nonzero defect and zero centre pairing, so that plan cannot close from U_3 relations and R ~= R^2 alone.
artifacts:
  - research/artifacts/rank-four-plan-adversarial-audit-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-r4-adversary`; verification requested from `w4-vf-gate`) by
`unipotent-frame-corner-cuntz-obstruction-proof`.

Let `K` be a finite field of characteristic `p` and `R` any unital `K`-algebra, `L_K(1,2)`
included. Let `U_4(R) <= EL_4(R)` be the unitriangular group and `N_IJ = rho(x_IJ(1)) - 1`.

1. **A model with nonzero defect.** There is a homomorphism `rho : U_4(R) -> GL_(p^2)(F_p)` with
   `rk(N_23 N_12) = (p-1)^2/p^2`, and with `N_13 = N_24 = N_14 = N_34 = 0`.
2. **The listed relations hold in it.** `rho` satisfies every relation Plan 1 lists: the isometry
   commutators on `(1,2)-(2,3)` and `(2,3)-(3,4)`, both readings of `x_14(abc)`, and
   `x_12(1) = x_12(e_0) x_12(e_1)`.
3. **No corner family.** In a ring with directly finite corners, `T_0 S_0 = e` and `T_0 S_1 = 0`
   inside `eMe` force `S_1 = 0`. So no nonzero corner carries `T_i S_j = delta_ij e`.

So no implication valid for all homomorphisms from `U_4(R)` into rank ultraproducts leads from
`N_23 N_12 != 0` to a corner Cuntz--Toeplitz family. Checks (a)--(c) of
`rank-four-isometry-relations-give-corner-cuntz-family` cannot be derived from relations of
`U_4(R)`. In `rho` the `x_14` data vanish, so check (c) fails while the defect has positive rank.

## Consequences

- **A proof must use `sigma` outside `U_4(R)`.** For `I < J`, `x_IJ(1) x_JI(-1) x_IJ(1)`
  conjugates `x_IJ(a)` to `x_JI(-a)`. So `U_4(R)` and one opposite unit root element generate
  `EL_2(R) = GL_2(R) ~= R^x` on `{I, J}` (`leavitt-gl-equals-el-and-perfect-unit-group`). The torus
  elements `diag(u,1,1,1)` form a copy of `R^x` too.
- **The fourth index adds coordinates, not relations.** `EL_4(R) = EL_3(R) = R^x` as abstract
  groups, through `R^2 ~= R`, so every `EL_4` relation is an `EL_3` relation.
- **Plan 2 dies as written.** The restriction of `rho` to `U_3(R)` has nonzero defect and zero
  centre pairing. The regular sofic model of `U_4(R)` has `rk(n_IJ(a)) = 1 - 1/p` at every position
  and nonzero centre data. So neither rank symmetry across positions nor nonvanishing centre data
  rescues a `U_3`-only argument. Only operator use of Weyl or opposite root elements escapes, and
  those generate a copy of `R^x`.
- **The route is not invalidated.** The claim's conclusion is contradictory in every rank
  ultraproduct, so the claim is equivalent to `N_23 N_12 = 0` for all rank models of `R^x`, read in
  the block frame. The route stays valid, and its content is the gate.

## Attempts

- **Plan 1's listed relations: die** (this node, artifact Section 1).
- **The claim restated:** it is equivalent to the defect identity, and check (a) alone is
  contradictory (artifact Section 2).
