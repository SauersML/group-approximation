---
rg: 2
id: boundary-char-two-nonhyperlinear-from-leavitt
kind: route
title: Use the characteristic-two boundary equivalence to inherit Leavitt nonhyperlinearity
target: boundary-char-two-simple-kazhdan-is-not-hyperlinear
requires:
  - binary-leavitt-unit-group-is-not-hyperlinear
  - leavitt-gl-equals-el-and-perfect-unit-group
  - boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
  - research/artifacts/sk-hyperlinear-boundary-a-reduction-2026-09-13.md
---

Fix finite k of characteristic 2, d>=2, and N>=3. Put R=L_(F_2)(1,2).
The three-leaf prefix coordinates and GL=EL identify R^x with EL_3(R),
which is therefore nonhyperlinear by the first prerequisite.

The boundary equivalence states, for precisely these parameters, that
S_boundary(d,k,N) is hyperlinear if and only if EL_3(R) is hyperlinear.
Its forward direction is enough: a proper boundary corner carries the
binary Leavitt algebra; padding elementary matrices by the complementary
identity gives a subgroup meeting the ambient scalar center trivially.
Elementary rank transport puts a copy of EL_3(R) in the projective boundary
group. Hyperlinearity passes to subgroups, a contradiction.

This implication uses an actual subgroup unaffected by the central
quotient. It does not infer nonhyperlinearity for arbitrary central
quotients, nor does it transfer the conclusion to other characteristics.

**Attribution.** The proposed analytic input upstream of the Leavitt
premise is Jihao Liu, [*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7, with the compatible expectation criterion of Proposition
3.1. The Leavitt and boundary consequences are Cairn's conditional
applications of Liu's analytic theorem, not statements attributed to his
paper. Their other ingredients are the earlier September 8 Cairn two-use
heat argument and the September 13 boundary subgroup reduction.
