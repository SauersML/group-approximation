---
rg: 2
id: binary-leavitt-units-over-any-field-are-not-hyperlinear
kind: claim
title: "The binary Leavitt unit group over every field is nonhyperlinear"
distinct_from:
  binary-leavitt-unit-group-is-not-hyperlinear: "That is the fixed F_2 group, with a separate internality-only proof; this covers every field, including characteristic zero and fields not finitely generated as rings."
  d-ary-leavitt-groups-nonsofic-over-finite-fields: "That is nonsoficity for arbitrary branching over finite fields; this asserts nonhyperlinearity for binary Leavitt algebras over every field."
artifacts:
  - research/artifacts/leavitt-all-fields-normalization-obstruction-2026-09-20.md
---

For every field k, the group L_k(1,2)^x is not hyperlinear. For an uncountable field this means failure of the usual finite-local matrix approximation property: the proof exhibits a countable finitely generated nonhyperlinear subgroup.

No finite presentation, simplicity or property (T) is asserted for the full unit group of an arbitrary field. The finitely generated witness is an elementary group over a finitely generated subring.

## Attribution

This is a Cairn application of Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), Theorem 1.2/6.7, and the conditional normalization theorem credited to Andreas Thom, [*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf), Theorem 1.2; see also Liu Theorem 1.3/7.4 and its priority discussion. The general-field Leavitt conclusion is not stated as Liu's theorem or an independently discovered analytic mechanism.

## Attempts

2026-09-20: the native compressor argument was checked independently in every characteristic. Finite elementary factorizations place the three required compressors in EL_4(S) for one finitely generated unital subring S. The proof deliberately uses k_+ itself for the killed-root witness, avoiding an unjustified assumption that an additional unit of M_4(S) is elementary. The analytic normalization prerequisite remains explicit in the route.
