---
rg: 2
id: fpbs-extension-routes-to-finite-cost-are-circular-proof
kind: route
title: Lift a cost-minimising action through the second projection of a product
target: fpbs-extension-routes-to-finite-cost-are-circular
requires: []
artifacts:
  - research/artifacts/fpbs-extension-certificates-carry-no-cost-information-2026-09-17.md
---

The proof is in §§1-2 of the artifact.
- Lifting a graphing through a factor map of free actions keeps its cost,
  and by freeness it still generates. This gives `C(e) <= C(b)`.
- Apply this to the projection `b x a_0 -> a_0`, with `a_0` a free action
  attaining `C(Gamma)`. This gives `C(b x a_0) <= C(Gamma)`. The reverse
  inequality holds because every free action costs at least `C(Gamma)`.
- The equivalences and the class kill follow by specialising to
  `c = a_0`.
- For the mixing choice of `a_0`, replace `a_0` by `a_0 x s` and lift
  again.
- §§3-4 of the artifact contain only cited examples: the finite-fibre bound,
  `F_inf x Z` via [G00] Props VI.9 and VI.23, and the coinduction formula
  over `M = Gamma_mal ⋊ Z`.

This is a supplied deduction, not external validation.
