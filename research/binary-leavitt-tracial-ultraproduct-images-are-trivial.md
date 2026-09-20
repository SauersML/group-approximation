---
rg: 2
id: binary-leavitt-tracial-ultraproduct-images-are-trivial
kind: claim
title: Every tracial matrix-ultraproduct homomorphism of the binary F_2 Leavitt unit group is trivial
distinct_from:
  binary-leavitt-unit-group-is-not-hyperlinear: "That excludes faithful canonical matrix models; this explicitly kills every element in every tracial matrix-ultraproduct homomorphism."
  leavitt-unit-group-has-only-trivial-sofic-morphisms: "That concerns sofic targets; this includes arbitrary hyperlinear targets and all tracial matrix-ultraproduct images."
  full-defect-rings-have-full-hyperlinear-radical: "That concerns elementary groups over general full-defect rings and need not kill their entire unit groups; this identifies the entire specified Leavitt unit group with such an elementary group."
artifacts:
  - research/artifacts/full-defect-ring-hyperlinear-radical-audit-2026-09-20.md
  - research/artifacts/leavitt-direct-normalization-obstruction-2026-09-20.md
---

Let H=L_(F_2)(1,2)^x. For every tracial matrix ultraproduct M and every homomorphism rho:H->U(M), rho is trivial. Equivalently, every homomorphism from H to any hyperlinear group is trivial.

## Attribution and attempts

2026-09-20: this follows from the full-defect ring theorem and the established GL=EL and complete-prefix-code identifications. The essential analytic theorem is Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), Theorem 1.2/6.7. Andreas Thom has priority for its [conditional normalization consequence](https://andreasthom.github.io/pdf/nonhyperlinear.pdf), Theorem 1.2. The Cohn/Leavitt normal-generation algebra is the earlier Cairn manuscript, not a theorem claimed by Liu. The earlier fixed-mark proof plus the separate simplicity theorem gives an alternate deduction, but simplicity is unnecessary for the full-defect route.

The additional native route `leavitt-trivial-images-via-native-commutators`
now writes the normal-generation chain explicitly, from x_13(e) to
x_43(b), x_42(1), and every x_12(r), followed by elementary permutations.
It uses the rank-four compression pair and normalization directly and
requires neither simplicity nor the more general full-defect theorem.
