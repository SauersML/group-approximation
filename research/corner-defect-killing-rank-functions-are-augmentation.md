---
rg: 2
id: corner-defect-killing-rank-functions-are-augmentation
kind: claim
title: A Sylvester rank function on the binary Leavitt unit group algebra that kills the two-root defect at one corner is the augmentation rank
distinct_from:
  two-root-identity-is-corner-local-for-leavitt-rank-models: that is corner locality for homomorphisms into rank ultraproducts; this is the same conclusion for every Sylvester matrix rank function on the group algebra, matricial or not.
  leavitt-rank-functions-killing-two-root-defect-are-augmentation: that decides a rank function by the defect at the unit pair; this decides it by the defect at any single proper corner, pulling back along the corner endomorphism and using simplicity of the unit group.
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-upg-audit`; verification requested from `w4-vf-gate`) by
`sylvester-corner-defect-augmentation-proof`.

Let `R = L_(F_2)(1,2)`, identify `R^x = EL_3(R)` through the three-leaf prefix code, and put
`D = ([x_23(1)] - 1)([x_12(1)] - 1)` in `F_2[R^x]`. For a proper prefix `P` let
`iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`, extended linearly. If a Sylvester matrix rank function `rk`
on `F_2[R^x]` has `rk(iota_P(D)) = 0` for one proper prefix `P`, then `rk` is the augmentation rank.

**Consequence.** For a homomorphism of `R^x` into the units of any ring with a faithful Sylvester rank
function, a vanishing corner product at one proper cylinder makes the homomorphism trivial. So
`two-root-identity-is-corner-local-for-leavitt-rank-models` holds for abstract targets, and the
compactness step of the defect gap needs no matrix approximations (artifact Section 1).

## Attempts

Established, not open. Proof in artifact Proposition 1.1.
