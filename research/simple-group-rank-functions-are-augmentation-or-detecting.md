---
rg: 2
id: simple-group-rank-functions-are-augmentation-or-detecting
kind: claim
title: On the group algebra of a simple group every Sylvester rank function is the augmentation rank or detects every nontrivial element
distinct_from:
  full-averaging-idempotent-kills-its-element-in-rank-models: that says a full averaging idempotent makes its element act trivially in every rank model; this classifies the Sylvester matrix rank functions on the group algebra of a simple group into the augmentation rank and rank functions detecting every nontrivial element, so that one non-augmentation rank function refutes every averaging corner of the group at once.
artifacts:
  - research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md
---

**ESTABLISHED.** Let `K` be a field, `Γ` a group and `rk` a Sylvester matrix rank function on `K[Γ]`.
- `N_rk = {x in Γ : rk(1 - [x]) = 0}` is a normal subgroup, and `rk` descends to `K[Γ/N_rk]`.
- If `N_rk = Γ`, then `rk(X) = rank_K(ε(X))` for every matrix `X`, where `ε` is the augmentation.
- So if `Γ` is simple, `rk` is either the augmentation rank or satisfies `rk(1 - [x]) > 0` for every
  `x != 1`.

**Consequence for averaging corners.**
- Quotienting by its null ideal turns every Sylvester rank function into a rank model, so
  `full-averaging-idempotent-kills-its-element-in-rank-models` applies to all of them.
- On a simple group `Γ`, a solution of `c e_H b = 1` for one nontrivial finite subgroup `H` of
  invertible order therefore leaves the augmentation rank as the only Sylvester matrix rank function
  on `K[Γ]`.
- For `Γ = R^x` over `F_2` (Corollary 1.3 of the artifact), the open claim
  `binary-leavitt-units-carry-nonaugmentation-rank-function` refutes both binary averaging targets,
  `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` and
  `thompson-v-order-three-averaging-idempotent-is-full`.

Proof: Theorem 1.1 of the artifact, route `simple-group-rank-function-dichotomy-proof`.
