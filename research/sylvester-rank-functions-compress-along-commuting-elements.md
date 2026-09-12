---
rg: 2
id: sylvester-rank-functions-compress-along-commuting-elements
kind: claim
title: Compressing a Sylvester rank function along an element commuting with a subalgebra gives a Sylvester rank function, and commuting nilpotents shrink it by a fixed factor
distinct_from:
  simple-group-rank-functions-are-augmentation-or-detecting: that describes the null normal subgroup of a rank function on a group algebra; this builds new rank functions from old ones by compressing along commuting elements, which forms corner models without idempotents.
  toeplitz-isometry-defects-have-total-rank-at-least-one: that is an inequality for isometry defects in any Sylvester rank function; this constructs rank functions and bounds commuting nilpotents through the Frobenius inequality.
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-c3-descent`; independent re-derivation requested from `w4-vf-gate`) by
`sylvester-commuting-compression-proof`.

Let `N` be a Sylvester matrix rank function on a unital ring `A`.
1. **Compression.** Let `phi : A' -> A` be a unital ring homomorphism, and let `P` in `A` commute with
   `phi(A')` and have `N(P) > 0`. Then `X -> N(phi(X) P)/N(P)` is a Sylvester matrix rank function on `A'`.
2. **Commuting idempotents.** If an idempotent `e` commutes with `P`, then `N(P) = N(eP) + N((1-e)P)`.
3. **Commuting nilpotents.** If `x` commutes with `P` and `x^m = 0`, then `N(xP) <= (1 - 1/m) N(P)`.
4. **Frobenius.** `N(XY) + N(YZ) <= N(Y) + N(XYZ)`.

**What is not used.** Regularity, faithfulness, images and annihilators. So the corner models `q M q` along
range idempotents, which the characteristic-two descent uses, have an abstract replacement: compress along
`P` itself.

**Consequences.**
* **Characteristic two.** Item 3 with `m = 2` gives the upper bounds of
  `nested-two-root-defect-pieces-decay-geometrically-both-ways` (`f(k+1) <= f(k)/2`) for every abstract
  Sylvester rank function, not only for faithful rank ultraproducts.
* **Characteristic three.** With `m = 3` it gives the bound `2/3` used for the ternary cylinder defects.

Proof: artifact Section 1, Lemmas 1.1 and 1.2.
