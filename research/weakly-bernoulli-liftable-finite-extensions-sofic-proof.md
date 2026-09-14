---
rg: 2
id: weakly-bernoulli-liftable-finite-extensions-sofic-proof
kind: route
title: Carry the extension cocycle on microstates of the lifted action transferred from Bernoulli microstates
target: weakly-bernoulli-liftable-finite-extensions-are-sofic
requires: []
artifacts:
  - research/artifacts/gk3-rokhlin-tester-2026-09-14-part2.md
---

Sections 2.1–2.3 of the part 2 artifact. Direct proof, no imported claims.

1. **Bernoulli microstates (Lemma T1).** Random iid labels on `V_n`, read through a cylinder approximation, have the
   right pattern law at good points, and concentrate by Chebyshev because patterns at `v` and `v'` are independent
   unless their windows meet.
2. **Transfer (Lemma T2).** Weak containment in the pattern form gives a partition of the Bernoulli shift with the same
   alphabet and nearby pattern law, and its microstates serve for `Y_0`.
3. **Cocycle.** A Borel section of `X_0 -> Y_0` defines `ν(w, y) ∈ N` with `ν(ww', y) = c_w(ν(w', y)) ν(w, π(w')y)`
   and `ν(m, y) = m` on `N`.
4. **Models.** `τ_n(w)(m, v) = (c_w(m) ℓ(v)_w, σ_n(π(w))v)` on `N × V_n`.
   - The cocycle identity fails only where the microstate pattern law is wrong.
   - `π(w) != 1` moves almost every `v`.
   - `w ∈ N` sends `(m, v)` to `(w m, v)`.
