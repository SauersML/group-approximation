---
rg: 2
id: fixed-host-outside-sofic-permanence-closure-proof
kind: route
title: The Leavitt unit group is a finitely presented simple nonsofic Kazhdan atom inside the host
target: fixed-host-outside-sofic-permanence-closure
requires: [sofic-permanence-closure-omits-simple-fa-nonsofic-groups, leavitt-unit-group-finitely-presented, binary-leavitt-unit-group-is-simple, openai-leavitt-unit-nonsofic, leavitt-gl-equals-el-and-perfect-unit-group, rank-twelve-leavitt-simple-non-mf, whitehead-universal-finitely-presented-container]
artifacts:
  - research/artifacts/fixed-host-permanence-closure-obstruction-2026-09-12.md
---

Put `Sigma = R^x`.
* Finitely presented: `leavitt-unit-group-finitely-presented`.
* Simple: `binary-leavitt-unit-group-is-simple`.
* Not sofic: `openai-leavitt-unit-nonsofic`.
* Property FA. A complete binary prefix code with twelve leaves identifies `R`
  with `M_12(R)`, so `R^x ~= GL_12(R) = EL_12(R)` by
  `leavitt-gl-equals-el-and-perfect-unit-group`. `EL_12(R)` has property (T)
  by `rank-twelve-leavitt-simple-non-mf`. Property (T) implies FA (Watatani
  1982; Bekka--de la Harpe--Valette, Theorem 2.12.4).

`sofic-permanence-closure-omits-simple-fa-nonsofic-groups` then excludes every
group containing `Sigma`. `R^x` is finitely presented, hence recursively
presented, so it embeds in `U` by
`whitehead-universal-finitely-presented-container`. Section 4 of the artifact
gives the details.
