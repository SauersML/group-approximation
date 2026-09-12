---
rg: 2
id: outer-state-rank-subadditivity-criterion-proof
kind: route
title: Check the Sylvester axioms on the outer s-rank, using the separated triangular lemma for the triangular bound
target: outer-state-rank-is-rank-function-iff-subadditive
requires:
  - separated-triangular-steps-flatten-to-minors
  - rank-functions-extending-a-state-are-pinned-on-regular-elements
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

Section 3 of the artifact.
1. **Idempotent minors.** From `f = L e R`, the maps `alpha = e R f` and `beta = f L e` give `beta alpha = f`,
   and `e' = alpha beta` is an idempotent under `e`. So `s(f) <= s(e)`.
2. **Minors and products.** Both follow because minors compose.
3. **Superadditivity.** `f (+) g <~ X (+) Y` whenever `f <~ X` and `g <~ Y`.
4. **Triangular bound.** `separated-triangular-steps-flatten-to-minors` with empty padding gives
   `f (+) g <~ [[X, C], [0, Y]]`.
5. **Minimality.** This is item 2 of `rank-functions-extending-a-state-are-pinned-on-regular-elements`.
