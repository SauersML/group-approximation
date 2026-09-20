---
rg: 2
id: leavitt-fp-simple-kazhdan-from-nonhyperlinearity
kind: route
title: Assemble the independent structural properties of the same Leavitt witness
target: binary-leavitt-is-fp-simple-kazhdan-nonhyperlinear
requires:
  - binary-leavitt-unit-group-is-not-hyperlinear
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
---

All prerequisites concern R=L_(F_2)(1,2) or apply to it. R is finitely
generated as a unital ring. Prefix-code matrix self-similarity and GL=EL
identify R^x with EL_4(R), so the elementary-group theorem supplies property
(T). The simplicity prerequisite gives infinite simplicity. Khanh's
separately imported theorem supplies finite presentation. The negative
prerequisite supplies nonhyperlinearity of this very group. No embedding
of one existential witness into another is used.

**Attribution.** The negative prerequisite conditionally uses Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorem 1.2/6.7, through the earlier Cairn Leavitt two-use argument.
H. V. Khanh supplies the separately named finite-presentation result;
this assembly does not credit either contribution to Cairn.
