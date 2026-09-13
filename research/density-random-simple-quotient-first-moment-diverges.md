---
rg: 2
id: density-random-simple-quotient-first-moment-diverges
kind: claim
title: The expected number of finite simple quotients of a density random group is infinite at every large length
distinct_from:
  convergent-quotient-count-decides-gromov-question: that shows a finite first moment over a finite family of hyperbolic groups decides Gromov's question; this shows the unconditioned first moment of the density model is infinite, through members that are not Kazhdan
  density-random-groups-no-finite-quotients-below-exp-k: that bounds the expected number of simple quotients below an order threshold; this shows the total expectation, over all orders, is infinite
artifacts:
  - research/artifacts/solve-hyperbolic-rf-2026-09-13.md
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty claimed).

**Setting.** Let `m >= 2`, `0 < d < 1/2` and `k = ⌊(2m−1)^(dL)⌋`. Let `R` be a uniform
`k`-subset (or `k` independent uniform choices) of the cyclically reduced words of
length `L` in `F_m`. For `Λ = F_m/<<R>>` let `X(Λ)` be the number of normal subgroups
with finite simple quotient, as in `convergent-quotient-count-decides-gromov-question`.

**THEOREM.** There is `L_0(m, d)` such that `E[X(Λ)] = ∞` for every `L >= L_0` with
`L ≡ 3 (mod 6)`.

The infinite contribution comes from relator sets inside `<<a_1^3>>`. Those members
surject onto `Z/3 * F_(m−1)`, which has infinite abelianization, so they are not
Kazhdan.

**Where counting stops.**
- `density-random-groups-no-finite-quotients-below-exp-k` bounds the part of `E[X]`
  below order `exp(c k)`. The total is infinite, so no bound on this unconditioned
  moment excludes all finite quotients, at any length.
- Condition on the event that `Λ` is non-elementary hyperbolic. What remains is a
  finite family of non-elementary hyperbolic groups with positive weights. By (C2) of
  `convergent-quotient-count-decides-gromov-question`, a finite conditioned
  expectation of `X` already gives an infinite hyperbolic Kazhdan group with no
  nontrivial finite quotient.
- So in this model the first-moment method either diverges or, after conditioning, is
  at least as strong as the target. What is left is structural: control of the simple
  quotients of the typical member, not of the average.

Proof: `density-random-first-moment-divergence-proof`.
