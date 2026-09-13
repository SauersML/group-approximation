---
rg: 2
id: steinberg-gl-mf-radical-is-commutator-or-trivial
kind: claim
title: The MF radical of GL_n over a Steinberg algebra is the whole commutator subgroup when the groupoid compresses every compact open set, and trivial when the algebra is exactly matricial
distinct_from:
  kazhdan-elementary-approximation-type-mirrors-ring-type: that is the open UN root about the approximation type of elementary groups over all simple rings; this is the established two-extremes statement for the full general linear groups over Steinberg algebras
  free-group-cantor-elementary-group-lef-iff-invariant-measure: that is the open flagship dichotomy for elementary groups over free-group crossed products; this is the unit-group face over arbitrary groupoids at the two extremes, with no exhaustiveness claim
artifacts:
  - research/artifacts/un-k1-homology-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route `steinberg-gl-mf-radical-is-commutator-or-trivial-proof`.

Let `𝒢` be a second countable, Hausdorff, ample, minimal, effective groupoid with compact infinite unit space,
`k` a countable field, `R = A_k(𝒢)`, and `n >= 1`.

1. **Paradox extreme.** If `𝒢` satisfies (PI) of `purely-infinite-steinberg-gl-max-mf-quotient-is-k1`, then
   `Rad_MF(GL_n(R)) = [GL_n(R), GL_n(R)]`. The maximal MF quotient `K_1(R)` is abelian and countable: an MF
   approximation of `GL_n(R)` sees only algebraic `K_1`.
2. **Measure extreme.** If `R` embeds unitally in an algebraic ultraproduct `∏_ω M_(d_k)(F_k)` over fields
   (exactly matricial), then `Rad_MF(GL_n(R)) = 1`: `GL_n(R)` is LEF, hence MF, sofic and hyperlinear.

The two hypotheses exclude each other. An exactly matricial ring is stably finite, while (PI) makes `1_X`
properly infinite.

**Calibrating pair.**
- **(1) holds:** the Cuntz groupoid, where `R = L_k(1,2)` and `GL_n(R)` has only the trivial MF quotient
  (`K_1 = 0`).
- **(2) holds:** the transformation groupoid of a minimal ℤ-subshift over `k = F_q`, where
  `R = LC(X, F_q) ⋊ ℤ`, the Pestov ring.

**Not claimed.** Exhaustiveness. Groupoids satisfying neither hypothesis form the middle ground. An example is
the free minimal ℤ²-SFT of Labbé, whose crossed product is simple, finitely generated and stably finite, but
whose exact matricial embeddability is open (`labbe-wang-shift-crossed-product-is-exactly-matricial`). There
the MF radical of `GL_n` is not determined by these results.
