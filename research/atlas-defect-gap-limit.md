---
rg: 2
id: atlas-defect-gap-limit
kind: claim
title: The atlas defect gap is positive at every multiplicity and converges — no magic multiplicities
distinct_from:
  atlas-true-criterion-baseline: that computes the objective exactly at two specific unitaries; this is a structural statement about the minimum over all of `U(20160k)` as `k` varies.
  leavitt-multiplicative-trace-floor: that is a dimension-free floor for four contractions in any finite matrix algebra, the ring-first obstruction; this is about the group-side atlas objective and asserts positivity at fixed `k` only, with no dimension-free constant claimed.
  leavitt-steinberg-hs-unstable: that is the branch selection — equivalently `inf_k d_k = 0`; this says only that the infimum is a limit and is attained-in-the-limit, which decides nothing.
artifacts:
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
---

For the explicit criterion of `atlas-steinberg-rank-five-translation` put

```text
d_k = min_{U ∈ U(20160k)}  max_{s ∈ T_St}  ‖π_U(s) − I‖₂ ,
```

with `π_U(h) = λ(h) ⊗ I_k` on the first chart and `U(λ(h) ⊗ I_k)U*` on the
second.  Then:

1. the minimum is attained and `d_k > 0` for every `k ≥ 1`;
2. `(k + ℓ) d_{k+ℓ}² ≤ k d_k² + ℓ d_ℓ²`, so `k ↦ k d_k²` is subadditive; and
3. consequently `lim_k d_k² = inf_k d_k²`.

Hyperlinearity of `Q` — equivalently `leavitt-steinberg-hs-unstable` — is the
statement `inf_k d_k = 0`, so (3) says the criterion has **no isolated magic
multiplicities**: a witness cannot hide at one exceptional `k` surrounded by
bad ones.  Either the defect decays along all large multiplicities, or it is
bounded below by a dimension-free constant and `Q` is nonhyperlinear.

This decides nothing — Fekete gives the limit, not its value, and no rate.
It is recorded because it is what makes multiplicity sweeps interpretable:
a measured `d_k` at small `k` is an upper bound for the limit only through
subadditivity, and an isolated good `k` would be a computational error rather
than a discovery.
