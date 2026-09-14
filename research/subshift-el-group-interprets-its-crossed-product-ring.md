---
rg: 2
id: subshift-el-group-interprets-its-crossed-product-ring
kind: claim
title: For an infinite minimal subshift, the ring LC(X,F_2)⋊Z is interpretable with parameters in the group EL_3 of that ring, with each root subgroup a centraliser of an explicit finite set
distinct_from:
  subshift-el-groups-boundedly-elementary-generated: that bounds how many elementary matrices a group element needs; this reads the ring off the group by first-order formulas, and uses no bound.
  marked-subshift-elementary-group-determines-language: that recovers the language of X from the marked group, an isomorphism-invariance statement; this is a first-order interpretation of the whole ring inside the abstract group.
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

**Statement.** Let `X` be an infinite minimal subshift over a finite alphabet, `R = LC(X,F_2) ⋊_T Z`, `G = EL_3(R)`, and `S = {1,u,u^{-1}} ∪ {e_a}` the usual finite generating set of `R` as a unital ring. Then

    U_13 = C_G({e_12(s) : s ∈ S} ∪ {e_23(s) : s ∈ S}),

and likewise for the other five root subgroups after permuting coordinates. Consequently `R` is interpretable in `G`, with the parameter list consisting of the `e_ij(s)` for `s ∈ S` and the two permutation matrices `P_12, P_23 ∈ G`: the domain is `U_13`, addition is the group operation, and multiplication is

    r·s  ↔  [ w_{12} e_13(r) w_{12}^{-1}, w_{23} e_13(s) w_{23}^{-1} ] = e_13(rs).

**Inputs.**
- `Z(R) = F_2`: a central element has `T`-invariant, hence constant, coefficients, and aperiodicity of `T` kills every `u^j` with `j ≠ 0`. This is where infiniteness and minimality of `X` enter, and the claim is false for periodic `X`.
- In characteristic 2 the transposition matrices `P_23 = e_23(1)e_32(1)e_23(1)` and `P_12 = e_12(1)e_21(1)e_12(1)` lie in `G`, and conjugation by them carries `e_ij(r)` to `e_{σ(i)σ(j)}(r)`.

**Scope.** No soficity, no property (T) and no simplicity of `G` is used. Nothing is claimed for `EL_2`, for other coefficient rings, or for the lamplighter hosts.

**Status: established** by `subshift-el-group-interprets-its-ring-proof`. UNREVIEWED; queued in the wave-12 verifier queue.
