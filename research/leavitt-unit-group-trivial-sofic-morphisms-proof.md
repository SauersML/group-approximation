---
rg: 2
id: leavitt-unit-group-trivial-sofic-morphisms-proof
kind: route
title: A simple nonsofic group has full sofic radical
target: leavitt-unit-group-has-only-trivial-sofic-morphisms
requires: [leavitt-gl-equals-el-and-perfect-unit-group, binary-leavitt-elementary-group-is-simple, openai-leavitt-unit-nonsofic]
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

1. The three-leaf prefix code identifies `R` with `M_3(R)`, so
   `R^x = GL_3(R) = EL_3(R)`, by the first prerequisite.
2. That group is simple, by the second.
3. The sofic radical is a normal subgroup, so it is `1` or everything.
4. A trivial radical makes a countable group sofic, by the disjoint-union and
   product amplification in Section 0 of the artifact. That contradicts the
   third prerequisite.
