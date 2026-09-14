---
rg: 2
id: dyadic-derived-full-groups-no-uniform-semifree-diameter-proof
kind: route
title: A free-semigroup pair in the N-ball forces growth rate at least 2^(1/N), which non-uniform exponential growth rules out
target: dyadic-derived-full-groups-no-uniform-semifree-diameter
requires:
  - dyadic-tower-subshift-full-group-non-uniform-growth
artifacts:
  - research/artifacts/sk-rauzy-intermediate-2026-09-14-part1.md
---

Artifact §1.
1. **Growth rate.** Let `G = [[T]]′`. For a finite generating set `S`, put `ω_S = lim_ℓ γ_S(ℓ)^(1/ℓ)`.
2. **A pair forces growth.** Suppose `a, b` lie in the `N`-ball of `S` and freely generate a free semigroup.
   - The `2^k` positive words of length `k` in `a, b` are pairwise distinct elements of `S`-length at most `Nk`.
   - So `γ_S(Nk) ≥ 2^k`, and `ω_S ≥ 2^(1/N)`.
3. **Conclusion.** `dyadic-tower-subshift-full-group-non-uniform-growth` gives `ω(G) = inf_S ω_S = 1`. So for every `N` there is a generating set `S` with `ω_S < 2^(1/N)`, and by step 2 its `N`-ball contains no free-semigroup pair.

Nothing specific to full groups is used: in any finitely generated group, a uniform semi-free diameter implies uniform exponential growth.
