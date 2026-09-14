---
rg: 2
id: ternary-anti-central-summand-has-no-finite-dimensional-images
kind: claim
title: The ternary Leavitt unit group has no nontrivial finite-dimensional representation, so its anti-central group algebra summand maps to no matrix algebra
distinct_from:
  ternary-leavitt-swap-problem-splits-at-central-involution: that proves the anti-central summand has no unital homomorphism to a nonzero commutative ring; this excludes every nonzero homomorphism to a matrix algebra over any field, through perfection, simplicity of the scalar quotient and Malcev's theorem.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

Let `G = L_(F_3)(1,2)^x`, `z = -1`, and `S_- = F_3[G]/(1 + [z])`.
- Every finite-dimensional representation of `G` over any field is trivial.
- Consequently every ring homomorphism from `S_-` to `M_n(k)`, `k` a field, is zero.

Every trace, rank function, determinant, character or augmentation-type map that factors through a
finite-dimensional image therefore vanishes on `S_-`. Such maps cannot obstruct
`ternary-anti-invariant-swap-corner-is-full` or `ternary-anti-central-unit-class-is-nonpositive`.

Proof: Theorem B(ii) of the artifact.
