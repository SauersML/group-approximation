---
rg: 2
id: central-hnn-tag-modulus-proof
kind: route
title: Double the killed word and adjoin the central sign by an automorphism of Z times C2
target: central-hnn-tag-transfers-hyperlinear-radical
requires: []
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

The reduced word v=w_1w_2 has infinite order in G_1*G_2 by free-product
normal form. In B=(G_1*G_2) times C2, the subgroup <v,J> is Z times C2.
The assignments v -> vJ and J -> J define an automorphism of this subgroup.
Its HNN extension is exactly the presentation in the claim. Britton's
lemma embeds B, so J remains a nonidentity involution; all displayed
generators commute with J, making it central in K.

Any matrix-ultraproduct homomorphism of K kills both copies of w and hence
v. The HNN relation then kills J. For approximate representations, the
restrictions to the two copies of G each have defect at most delta. Thus
||v-I||_2 <= 2 kappa_G(delta). The HNN relator gives
||tvt^-1-vJ||_2 <= delta, and multiplication by v^-1 yields

```
||J-I||_2 <= delta + ||tvt^-1-v||_2
           <= delta + 2 ||v-I||_2
           <= delta + 4 kappa_G(delta).
```

If kappa_G(delta) did not tend to zero, assignments with defects tending
to zero and a uniform positive w-distance would give a forbidden
matrix-ultraproduct homomorphism. This proves the final assertion.

For the involution specialization, <w,J> in G times C2 is C2 times C2.
The same map w -> wJ,J -> J is an automorphism, so Britton and centrality
work identically without a free product. The estimate uses
||w-I||_2 <= kappa_G(delta) directly, giving the factor two instead of four.

This makes explicit the familiar central-sign HNN construction used in the
Paddock--Slofstra Proposition 5.8 reduction; the estimate is elementary
unitary-norm bookkeeping, not a new analytic input replacing Liu.
