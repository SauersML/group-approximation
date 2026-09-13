---
rg: 2
id: leavitt-unit-bernoulli-no-sofic-host-proof
kind: route
title: The unit group is infinite, simple, Kazhdan and nonsofic, so a host of its Bernoulli relation contains it and is not sofic
target: leavitt-unit-bernoulli-relations-have-no-sofic-host
requires:
  - simple-kazhdan-bernoulli-relation-hosts-contain-the-group
  - binary-leavitt-unit-group-is-simple
  - universal-leavitt-el4-nonsofic
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/solve-sofic-actions-2026-09-13.md
---

# Proof

1. **`K` is infinite and simple:** `binary-leavitt-unit-group-is-simple`.
2. **`K` has property (T).** `universal-leavitt-el4-nonsofic` (`ambient_full_profile`)
   gives property (T) for `EL_4` of the binary Leavitt algebra
   `L = L_(F_2)(1,2)`. By `leavitt-gl-equals-el-and-perfect-unit-group`,
   `GL_4(L) = EL_4(L)`. A complete prefix code with four leaves identifies `L`
   with `M_4(L)` as unital rings, so `GL_4(L) ≅ K` (the identification that node
   uses for `universalLeavittUnits_not_isSofic`). Property (T) is invariant
   under isomorphism.
3. **`K` is not sofic:** `universal-leavitt-el4-nonsofic`
   (`universalLeavittUnits_not_isSofic`).
4. **Conclusion.** Suppose `θ` carried the Bernoulli relation of `K` into
   `R_G|_A` for an essentially free p.m.p. action of `G`. By steps 1–2 and
   `simple-kazhdan-bernoulli-relation-hosts-contain-the-group`, `K` embeds in
   `G`. Subgroups of sofic groups are sofic, so step 3 makes `G` nonsofic. So no
   sofic `G` admits such a `θ`. ∎
