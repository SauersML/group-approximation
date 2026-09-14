---
rg: 2
id: two-order-three-coset-ideals-never-contain-one
kind: claim
title: Over any group, the right ideals of two order-three averaging idempotents never sum to the whole binary group algebra
distinct_from:
  rank-deficient-tower-coverings-decide-binary-cyclic-corner: that is the certificate form, with r < 3^k conjugate tower ideals deciding the binary cyclic corner; this proves that the smallest case, r = 2 with k = 1 and group-element left factors, never occurs in any group.
  finite-subgroup-idempotent-ideals-admit-no-proper-group-shift: that concerns a single finite-subgroup idempotent shifted by one group element; this concerns the sum of the right ideals of two different order-three subgroups.
artifacts:
  - research/artifacts/gk3-binary-fullness-2026-09-14.md
---

**ESTABLISHED** by `two-order-three-coset-ideals-proof` (lane gk3-binary-fullness, 2026-09-14; not independently
re-derived yet).

Let `G` be any group, `K_1`, `K_2` subgroups of order three, and `e_(K_j) = Σ_(h in K_j) [h]` in `A = F_2[G]`. Then
`1` is not in `e_(K_1) A + e_(K_2) A`.

**General form (same proof).**
- (a) For any two nontrivial finite subgroups `K_1`, `K_2` of odd order, `1` is not in `e_(K_1) A + e_(K_2) A`.
- (b) For nontrivial finite subgroups `K_1, ..., K_r` of odd order whose generated subgroup is their free product,
  `1` is not in `Σ_j e_(K_j) A`.

**Consequence.** In `rank-deficient-tower-coverings-decide-binary-cyclic-corner`, a coset certificate needs
`k >= 2`, `3 <= r < 3^k`, and conjugates `K_j` of `C_3^k` that satisfy relations beyond their free product.

**Scope.** The proof is combinatorial and uses no soficity, no approximation and nothing about `G` beyond the
subgroups. Over `F_2` it only needs the orders `|K_j|` to be odd.

## Attempts

Established, not open. Proof in artifact Section 3.
