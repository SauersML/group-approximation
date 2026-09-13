---
rg: 2
id: sl3-norm-drift-excludes-finite-almost-invariant-configs-proof
kind: route
title: A concavity estimate for elementary matrices on unit vectors, summed over a finite set permuted by bijections
target: sl3-norm-drift-excludes-finite-almost-invariant-configs
requires: []
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-2026-09-13.md
---

Full proof: Section 2 of the artifact.

1. **Reduction to unit vectors.** Take a unit `w` with `||xw|| = ||x||` and put `u = xw/||x||`. Then
   `||sx|| >= ||x||·||su||`.
2. **Pairs.** From `e_ij^(±1)u = u ± u_j e_i`, we get `||e_ij u||^2 ||e_ij^(−1)u||^2 = (1+a)^2 − 4ab`,
   with `a = u_j^2` and `b = u_i^2`. This is `>= 1 − 2a + 5a^2 > 0`.
3. **Concavity.** For fixed `j`, the two `b`'s sum to `1 − a`, and `b ↦ log((1+a)^2 − 4ab)` is concave. So
   the pair sum is at least `log((1 − 2a + 5a^2)(1+a)^2) = log(1 + 2a^2 + 8a^3 + 5a^4) = f(a) >= 0`.
   Here `f` is increasing and some `u_j^2 >= 1/3`, so `Σ_s log||su|| >= f(1/3)/2 = (1/2) log(128/81)`.
4. **Summation.** Put `N = log||Φ||`. Bijectivity gives `Σ_ω Σ_s [N(τ_sω) − N(ω)] = 0`. Write each term as
   `[N(τ_sω) − log||sΦ(ω)||] + [log||sΦ(ω)|| − N(ω)]`. The second parts sum to `>= κ|O|` by step 3. The
   first parts are `>= −η` on good pairs and `>= −B` on bad ones. So `0 >= κ|O| − 12η|O| − 12θB|O|`.
5. **Metric form.** If `d(Φ(τ_sω), sΦ(ω)) < ε`, then `Φ(τ_sω) = e·sΦ(ω)` with `d(e,1) < ε` by
   right-invariance. So `N(τ_sω) >= log||sΦ(ω)|| − log||e^(−1)||`. ∎
