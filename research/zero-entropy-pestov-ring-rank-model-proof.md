---
rg: 2
id: zero-entropy-pestov-ring-rank-model-proof
kind: route
target: zero-entropy-subshift-pestov-ring-has-rank-model-by-growth
requires:
  - subexponential-growth-simple-algebras-have-rank-models
artifacts:
  - research/artifacts/un-open-4-amenable-rank-models-2026-09-13.md
title: Proof — the generator ball of the crossed product is bounded by window length times complexity
---

Take the generating set `S = {χ_([a]) : a ∈ A} ∪ {u, u^{-1}}`, which generates `R = LC(X,F_q) ⋊_T Z` as a
ring because cylinder indicators of length `m` are products of shifted letter cylinders,
`u χ_Y u^{-1} = χ_(TY)`.

A word of length `≤ m` in `S` normalizes, using `u f = (f ∘ T^{-1}) u`, to `f · u^j` with `|j| ≤ m` and `f` a
product of at most `m` shifted letter cylinders, each supported in the window `[−m, m]`. So `f` lies in the
span of indicators of cylinders on that window, of dimension `p(2m+1)`. Hence

  `dim R_m ≤ (2m+1) · p(2m+1)`.

If `p` has subexponential growth so does `m ↦ (2m+1)p(2m+1)`, so `R` has subexponential growth and
`subexponential-growth-simple-algebras-have-rank-models` applies; `R` is simple for an infinite minimal
subshift. For Sturmian `X`, `p(n) = n+1` gives `dim R_m = O(m^2)`, so `GKdim R ≤ 2`; it is exactly `2`
because `R` is infinite dimensional and affine simple algebras of GK dimension `1` are PI, hence finite
dimensional when simple.

Details in §3, Calibration A, of the artifact.
