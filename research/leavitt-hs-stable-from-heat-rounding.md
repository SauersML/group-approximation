---
rg: 2
id: leavitt-hs-stable-from-heat-rounding
kind: route
title: Transfer Leavitt unit-group nonhyperlinearity to the stable Steinberg branch
target: leavitt-steinberg-hs-stable
requires:
  - binary-leavitt-unit-group-is-not-hyperlinear
  - leavitt-gl-equals-el-and-perfect-unit-group
  - steinberg-hs-stability-equals-nonhyperlinearity
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
---

For R=L_(F_2)(1,2), the four-leaf prefix coordinates give
R^x isomorphic to GL_4(R), and GL=EL identifies this with Q=EL_4(R).
Thus the first prerequisite makes Q nonhyperlinear. Condition 3 implies
condition 1 of `steinberg-hs-stability-equals-nonhyperlinearity`: St_5(R)
is normalized-HS stable in the strict same-dimension sense.

This consumes the established equivalence with Q; it does not transfer
nonhyperlinearity from an arbitrary quotient to its cover. The existing
`leavitt-steinberg-stable-branch` route then reaches `non-hyperlinear-group`.
The new negative premise remains dependent on open Kazhdan internality.

**Attribution.** The proposed analytic source of the negative premise is
Jihao Liu, [*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7, with Proposition 3.1 supplying the related expectation
criterion. Leavitt nonhyperlinearity and the stability consequence here are
Cairn's conditional downstream applications, not theorems claimed in Liu's
paper. The earlier September 8 Cairn two-use proof and the separately
recorded Steinberg stability equivalence provide the additional deductions.
