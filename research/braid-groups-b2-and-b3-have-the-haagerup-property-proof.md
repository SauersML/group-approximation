---
rg: 2
id: braid-groups-b2-and-b3-have-the-haagerup-property-proof
kind: route
title: B_3 contains F_2 x Z with index 6
target: braid-groups-b2-and-b3-have-the-haagerup-property
requires: []
artifacts:
  - research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md
---

`B_1 = 1` and `B_2 ≅ Z` have the property (Haagerup 1979 for free groups).

For `B_3`, Artin combing gives `P_3 ≅ F_2 ⋊ P_2`, with `P_2 = ⟨Δ_2²⟩` and `F_2` the loops of the third strand
around the first two. The full twist `Δ_2²` of the first two strands is the boundary twist of the
twice-marked disk, and it acts on `F_2` as conjugation by the loop `w` around both points. So `t' = w^{-1} Δ_2²`
centralizes `F_2`, and `P_3 = F_2 × ⟨t'⟩ ≅ F_2 × Z`. Free groups have the property, finite products preserve
it, and `[B_3 : P_3] = 6`, so induction to the finite-index overgroup preserves it.

Full text: §1 and §5 of `research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md`.
