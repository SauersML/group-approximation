---
rg: 2
id: sylvester-rank-functions-have-a-uniform-two-root-defect-gap
kind: claim
title: Every Sylvester rank function on the binary Leavitt unit group algebra that moves a generator by eta gives the corner defect rank at least c(eta)
distinct_from:
  leavitt-rank-model-defect-gap-on-fixed-point-free-quotients: that is the gap for homomorphisms into rank ultraproducts, normalized on fixed-point-free quotients; this is a displacement-to-defect gap for every Sylvester matrix rank function on the group algebra, by compactness of the space of rank functions, with no quotient normalization.
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-upg-audit`; verification requested from `w4-vf-gate`) by
`sylvester-two-root-defect-gap-compactness-proof`.

Let `R = L_(F_2)(1,2)`, `g_1, ..., g_4` generators of `R^x`, and `D` the two-root defect in `F_2[R^x]`
at the three-leaf identification. For every `eta > 0` there is `c^Syl(eta) > 0` such that every
Sylvester matrix rank function `rk` on `F_2[R^x]` with `max_i rk(1 - [g_i]) >= eta` has
`rk(iota_P(D)) >= c^Syl(eta)` for every proper prefix `P`. The value `rk(iota_P(D))` does not depend on
`P`.

**Scope.** Convex combinations with the augmentation rank force `c^Syl(eta) -> 0` as `eta -> 0`. The
constant is not explicit.

## Attempts

Established, not open. Proof in artifact Proposition 4.1.
