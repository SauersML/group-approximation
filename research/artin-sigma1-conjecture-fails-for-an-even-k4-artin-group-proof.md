---
rg: 2
id: artin-sigma1-conjecture-fails-for-an-even-k4-artin-group-proof
kind: route
title: Combine Sigma^1 membership with the living-subgraph computation for K
target: artin-sigma1-conjecture-fails-for-an-even-k4-artin-group
requires:
  - artin-k4-mixed-dead-character-lies-in-sigma1
---

Membership is `artin-k4-mixed-dead-character-lies-in-sigma1`.

The living subgraph is computed with the definition in
`artin-sigma1-is-connected-dominant-living-subgraph`: a dead edge has an even label
`>= 4` and `χ(u) + χ(v) = 0`.
- Every vertex has `χ != 0`, so `Liv_0^χ = K` and dominance is automatic.
- The four cross edges have labels `4, 4, 4, 6` and `χ`-sum `0`, so they are dead.
- `u1u2` and `v1v2` have label 2, so they are not dead.

Hence `Liv^χ` is the two disjoint edges `u1u2` and `v1v2`, and the conjecture
predicts `[χ] ∉ Σ^1`. Kochloukova states this prediction explicitly for this group:
arXiv:2009.14269, §7, Example 1, quoted in the membership claim.
