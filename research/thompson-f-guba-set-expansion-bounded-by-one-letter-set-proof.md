---
rg: 2
id: thompson-f-guba-set-expansion-bounded-by-one-letter-set-proof
kind: route
title: Each new letter x_j of X_k repeats a shifted copy of the previous layer, so layer increments grow at most by the factor k
target: thompson-f-guba-set-expansion-bounded-by-one-letter-set
requires: []
artifacts:
  - experiments/thompson-f-2026-09-17/layer_increment_check.py
---

**Setting.** `M` is the positive monoid of `F`, with relations `x_j x_i = x_i x_(j+1)` for
`i < j`. `M` is cancellative, so `|g W| = |W|` for every `g ∈ M` and every finite `W ⊆ M`.
Here `Z_(n+1) = Y`, `Z_k = X_k Z_(k+1)`, `t_k = |Z_k|` and `e_k = t_k - t_(k+1)`.

**Step 0.** `e_0 = 0`, because `Z_0 = x_0 Z_1` and left multiplication is injective.

**Step 1: e_k <= k e_(k+1) for 1 <= k <= n-1.** Put `W = Z_(k+2)`, so `Z_(k+1) = X_(k+1) W`.
Put `A_i = x_i Z_(k+1)` for `0 <= i <= k`. Then `Z_k = A_0 ∪ ... ∪ A_k` and `|A_i| = t_(k+1)`.

Fix `j` with `1 <= j <= k`. For `w ∈ W` the relation gives `x_j x_0 w = x_0 x_(j+1) w`. Since
`j+1 <= k+1`, `x_(j+1) w ∈ X_(k+1) W = Z_(k+1)`, so `x_j x_0 W ⊆ A_0`. Also `x_0 W ⊆ Z_(k+1)`,
so `x_j x_0 W ⊆ A_j`. Therefore

`|A_j \ (A_0 ∪ ... ∪ A_(j-1))| <= |A_j| - |x_j x_0 W| = t_(k+1) - t_(k+2) = e_(k+1)`.

Summing over `j = 1, ..., k` gives `t_k <= |A_0| + k e_(k+1) = t_(k+1) + k e_(k+1)`, which is
`e_k <= k e_(k+1)`.

*Sharper form.* The same relation gives `x_j X_(j-1) W = X_(j-1) x_(j+1) W ⊆ A_0 ∪ ... ∪ A_(j-1)`.
So the new part of `A_j` has size at most `t_(k+1) - |X_(j-1) W|`. For `k = 2`, `n = 3`
(`W = Y`) this gives `e_2 <= 2 t_3 - |Y| - |X_1 Y|`, which is `|X_2 X_3 Y| <= 3|X_3 Y| - |Y| - |X_1 Y|`.

**Step 2: one-letter reduction.** Let `n = m+d-1`. Iterating step 1 downward from `k = n-1`,

`e_(n-j) <= (n-1)(n-2) ... (n-j) e_n = (n-1)!/(n-1-j)! · e_n` for `0 <= j <= d-1`.

Every index used satisfies `n - j >= m >= 1`. Now
`|X_m ... X_n Y| - |Y| = t_m - t_(n+1) = sum_(j=0)^(d-1) e_(n-j) <= c(m,d) e_n`, and
`e_n = |X_n Y| - |Y|`. Finally, `X_m X_(m+1) ... X_(m+d-1)` equals `S_(m+1,m+d+1)` as a subset of
`M`. The inclusion `⊇` holds because normal forms are products of their letters. For `⊆`,
bring a product `x_(a_1) ... x_(a_d)` with `a_t <= m+t-1` to normal form by the relation. A swap
`x_a x_b -> x_b x_(a+1)` with `b < a` moves the smaller letter left and raises the larger by one,
so the letter now at position `t` is at most `m+t-1`.

**Step 3: consequences.** (a) If `|X_n Y| < (1 + 1/c)|Y|`, step 2 gives `|S Y| < 2|Y|`. So `S`
is not doubling, and item 3 of `thompson-f-nonamenable-iff-some-monomial-set-doubles` solves
`P_(d,m)`. (b) is the contrapositive. (c) applies step 2 to an optimal `Y ⊆ M_D` of either set.
`X_n` and `S` are homogeneous, so the counts stay inside fixed degrees.

**Check.** `experiments/thompson-f-2026-09-17/layer_increment_check.py` (random sets and optimal
`X_2` sets, 0 violations). The equality `Λ_(S_(2,4))(D) = 2Λ_(X_2)(D) - 1` for `D <= 10` is read
off the exact tables in `thompson-f-monomial-doubling-ratio-is-a-finite-computation`.
