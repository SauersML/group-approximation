---
rg: 2
id: bauer-strict-comparison-unit-division-is-local-proof
kind: route
title: Fix the finite cover first, then one precision for all levels, and orthogonalize by strict comparison
target: bauer-strict-comparison-unit-division-is-local
requires:
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

Proposition D of the part 2 artifact.
- Compactness gives closed neighbourhoods `Y_1, …, Y_L` whose interiors cover `K`, with
  the unit dividing over each.
- **Levels.** Use the `Y_k` as the levels of Section 3 of the part 2 artifact, with a
  partition of unity `supp h_k ⊆ int Y_k`.
- **Precision.** Because `L` is fixed before the precision, choose one `(N, δ)` with
  `L(6 d^{1/2} + δ) ≤ ε/2`, where `d = 1/(4N) + δ`. Take order zero maps `δ`-good on
  each `Y_k`.
- **Construction.** Steps 3–7 apply verbatim:
  - central staircases (Lemma 3 of the first artifact);
  - moves by strict comparison and Rørdam's lemma into exact orthogonal complements;
  - additivity of ranks over the orthogonal pieces.
- **Conclusion.** They give `W ∈ A` with `n[W] ≤ [1] ≤ (n+1)[W]` for every `n`. Item 3 ⟹
  item 1 of `strict-comparison-unit-divisibility-equivalences` divides the unit. ∎
