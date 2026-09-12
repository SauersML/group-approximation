---
rg: 2
id: two-root-identities-give-el3-ring-rigidity
kind: route
title: The two root identities give matrix units, matrix units extract a ring rank model, and the hypothesis forbids one
target: el3-rank-models-factor-through-ring-rank-models
requires:
  - rank-models-of-el3-satisfy-the-two-root-identities
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Why sufficient (artifact Section 3):

- **Identities give matrix units.** Take `sigma : EL_3(R) -> M^x`, with `R` of characteristic
  `p` having no ring rank model and `M` a characteristic-`p` rank ultraproduct. By the first
  prerequisite `sigma` satisfies `N_12^2 = 0` and `N_23 N_12 = 0`, and by the second its unit
  root elements act by matrix units.
- **Matrix units extract a ring rank model.** By the third, `p_1 != 0` gives a unital ring
  homomorphism from `R` into a rank ultraproduct. The hypothesis forbids that, so `p_1 = 0` and
  `sigma` is trivial.
- **Simplicity isn't used here.** The gate claim's simplicity hypothesis plays no part in this
  route.
- **Intended equivalence cycle.** This route and `el3-ring-rigidity-gives-the-two-root-identities`
  form an intended cycle. Neither claim establishes the other on its own.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 35 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
