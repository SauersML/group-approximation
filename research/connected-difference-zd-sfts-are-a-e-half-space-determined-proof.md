---
rg: 2
id: connected-difference-zd-sfts-are-a-e-half-space-determined-proof
kind: route
title: Flexibility below one level forbids flexibility far above it, so the lowest flexible level is an equivariant height, which no invariant measure can carry
target: connected-difference-zd-sfts-are-a-e-half-space-determined
requires: [sft-connected-differences-iff-flexible-sets-stay-close]
---

The notation is that of the target. Scale `n` so that `|n|_2 = 1`. Let `r` be the window radius
of `X`, and put `M = max(m, 2r) + 1`.

**Levels.**
- `x` is *down-flexible at `c`* if some `y ≠ x` in `X` has `y = x` on `H_c^+`. Then `x` is
  flexible on `{⟨p, n⟩ < c}`.
- `x` is *up-flexible at `c`* if some `w ≠ x` has `w = x` on `H_c^-`. Then `x` is flexible on
  `{⟨p, n⟩ > c}`.
- Both are monotone: down-flexible at `c` gives down-flexible at every `c' >= c`, since
  `H_(c')^+ ⊆ H_c^+`. Up-flexible at `c` gives up-flexible at every `c' <= c`.
- Put `a(x) = inf{c : x down-flexible at c}` and `b(x) = sup{c : x up-flexible at c}`, both in
  `[-∞, +∞]`.

**Step 1: `b(x) <= a(x) + M`.** Suppose `x` is down-flexible at `c` and up-flexible at `c'`, with
`c' > c + M`.
- The regions `{⟨p, n⟩ < c}` and `{⟨p, n⟩ > c'}` are at `ℓ^1` distance
  `>= ℓ^2 distance > c' - c > M > max(m, 2r)`.
- Part 2 of `sft-connected-differences-iff-flexible-sets-stay-close` gives a difference set that
  is not `m`-connected. This is a contradiction.
- By monotonicity, `b(x) <= a(x) + M`.

**Step 2: the three sets.**
- *`a(x) = +∞`.* `x` is down-flexible at no level, so it is determined by every `H_c^+`. This is
  `X_n^+`.
- *`a(x) = -∞`.* By step 1, `b(x) = -∞`. So `x` is up-flexible at no level and is determined by
  every `H_c^-`. This is `X_n^-`.
- *`a(x)` finite.* This is `X_n^0`.

**Step 3: measurability and equivariance.**
- `{x : x down-flexible at c}` is the projection to the first coordinate of
  `{(x, y) ∈ X^2 : y|H_c^+ = x|H_c^+}` intersected with `⋃_p {x(p) ≠ y(p)}`. That set is
  `σ`-compact, so the projection is `σ`-compact, hence Borel.
- By monotonicity, `a(x) = inf` over rational `c`. So `a` is Borel, and so are the three sets.
- A translate `v.x` is down-flexible at `c` iff `x` is down-flexible at `c ∓ ⟨v, n⟩`, with the
  sign fixed by the action convention. So `a(v.x) = a(x) ± ⟨v, n⟩`, and all three sets are
  invariant.

**Step 4: `μ(X_n^0) = 0`.** Let `μ` be an invariant probability measure.
- Since `n ≠ 0`, pick `v ∈ Z^d` with `s = |⟨v, n⟩| > 0`.
- The sets `E_k = {x ∈ X_n^0 : a(x) ∈ [ks, (k+1)s)}`, for `k ∈ Z`, are disjoint, Borel, and cover
  `X_n^0`.
- Translation by `v` (or `-v`) maps `E_k` onto `E_(k+1)`, so all `E_k` have the same measure.
- Countably many disjoint sets of equal measure in a probability space all have measure `0`.
- For ergodic `μ`, the invariant sets `X_n^±` then have measure `0` or `1`, and their union is
  conull. `∎`

**Remark.** The argument uses only coarse connectivity and finite type. Minimality and freeness
are not used.
