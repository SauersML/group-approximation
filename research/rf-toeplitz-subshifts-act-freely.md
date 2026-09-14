---
rg: 2
id: rf-toeplitz-subshifts-act-freely
kind: claim
title: The residually finite Toeplitz subshift over a residually finite group is free at every point, as an extension of the free odometer
distinct_from:
  rf-toeplitz-subshifts-over-residually-finite-groups: that proves minimality, residual finiteness and a free dense orbit, i.e. topological freeness; this proves trivial stabilizers at every point, which the self-contained tower proof of simplicity uses.
---

**ESTABLISHED (unreviewed).** Let `Γ`, the chain `Γ_m` and `X_Γ` be as in
`rf-toeplitz-subshifts-over-residually-finite-groups` (one hole coset per level; a `1`-subcoset and a `0`-subcoset
inside each hole).
- Every `y ∈ X_Γ` has, for each `m`, exactly one coset `D_m(y)` of `Γ_m` on which `y` is not constant.
- `D_(m+1)(y) ⊆ D_m(y)` and `D_m(g·y) = gD_m(y)`.
- So `y ↦ (D_m(y))_m` is an equivariant factor map onto the odometer `lim Γ/Γ_m`, and the action on `X_Γ` is free.

Route: `rf-toeplitz-subshifts-act-freely-proof`.

**Review (sk-verify-3, 2026-09-13): PASS.** The unique non-constant coset at every level for every limit point, nesting, equivariance and freeness re-derived. See `research/artifacts/sk-review-3-2026-09-13-part3.md` §A3.

**Review (sk-verify-4, 2026-09-13): PASS, independent concurrence.** (F1)/(F2) from the Theorem T construction, the fixed residue along a subsequence, and uniqueness, nesting, equivariance and freeness re-derived. See `research/artifacts/sk-review-4-2026-09-13-part1.md` §4.
