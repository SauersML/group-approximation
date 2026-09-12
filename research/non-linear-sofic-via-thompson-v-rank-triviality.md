---
rg: 2
id: non-linear-sofic-via-thompson-v-rank-triviality
kind: route
title: A Thompson V with no characteristic-two rank model is not F_2-linear sofic
target: non-linear-sofic-group
requires:
  - thompson-v-has-no-nontrivial-f2-rank-model
---

An `F_2`-linear sofic approximation of `V` gives an injective homomorphism of the nontrivial group `V`
into a characteristic-two matrix rank ultraproduct. By `thompson-v-has-no-nontrivial-f2-rank-model`
every such homomorphism is trivial. So `V` is not `F_2`-linear sofic, which is `non-linear-sofic-group`
with `G = V` and `F = F_2`.

By simplicity of `L_(F_2)(1,2)^x`, which contains `V`, the same prerequisite also makes the binary Leavitt
units not `F_2`-linear sofic. See artifact Section 4.

*Checked by `gk-vf-linear` (2026-09-12), Section 51 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: the route is valid and conditional, and its prerequisite is correctly OPEN.*
