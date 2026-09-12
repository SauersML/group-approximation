---
rg: 2
id: leavitt-unit-group-trivial-sofic-morphisms-proof
kind: route
title: A simple nonsofic group has full sofic radical
target: leavitt-unit-group-has-only-trivial-sofic-morphisms
requires: [leavitt-gl-equals-el-and-perfect-unit-group, binary-leavitt-elementary-group-is-simple, openai-leavitt-unit-nonsofic, sofic-radical-soficization]
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

1. The three-leaf prefix code identifies `R` with `M_3(R)`, so
   `R^x = GL_3(R) = EL_3(R)`, by the first prerequisite.
2. That group is simple, by the second.
3. `Rad_sof(R^x)`, the intersection of kernels of homomorphisms to sofic
   groups, is normal, so it is `1` or everything.
4. By `sofic-radical-soficization`, a trivial radical would make `R^x` sofic,
   contradicting the third prerequisite.

The finitary radical of the artifact, elements killed at density one in all
almost-multiplicative permutation models, is the same subgroup. A homomorphism
into a metric ultraproduct of symmetric groups has a countable, hence sofic,
image. Conversely, a sofic quotient embeds in such an ultraproduct. Section 0 of
the artifact records the amplification behind the finitary form.
