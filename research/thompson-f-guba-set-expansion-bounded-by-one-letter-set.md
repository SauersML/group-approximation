---
rg: 2
id: thompson-f-guba-set-expansion-bounded-by-one-letter-set
kind: claim
title: The expansion of every Guba monomial set S_(m+1,m+d+1) of Thompson's F is bounded by an explicit multiple of the expansion of the single letter set X_(m+d-1)
distinct_from:
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes the optimal ratio of one monomial set in one degree inside a finite universe; this is an inequality between the expansions of different sets on the same finite Y, valid in every degree and outside any universe.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that makes doubling of some S_(m+1,m+d+1) equivalent to non-amenability; this converts a doubling S_(m+1,m+d+1) into an explicit expansion constant 1/c(m,d) for the letter set X_(m+d-1), and a small-expansion set for that letter set into a certificate for P_(d,m).
  thompson-f-p22-monomials-admit-no-private-pivot-order: that rules out one ordering argument for the nine monomials of P_(2,2); this is a counting inequality for all Y and says nothing about pivot orders.
artifacts:
  - experiments/thompson-f-2026-09-17/layer_increment_check.py
  - experiments/thompson-f-2026-09-17/x2_optimal_D5_L7.txt
---

**ESTABLISHED** through `thompson-f-guba-set-expansion-bounded-by-one-letter-set-proof`
(direct elementary proof; not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, with relations `x_j x_i = x_i x_(j+1)` for `i < j`. Put
`X_k = {x_0, ..., x_k}`. By V. Guba, arXiv:2305.07113v4, §3, the monomial set of Problem
`P_(d,m)` is `S_(m+1,m+d+1) = X_m X_(m+1) ... X_(m+d-1)` (normal forms with
`i_1 <= m, ..., i_d <= m+d-1`). Let `Y ⊆ M` be finite and nonempty, and `n >= 1`. Define
`Z_(n+1) = Y` and `Z_k = X_k Z_(k+1)`, `t_k = |Z_k|`, `e_k = t_k - t_(k+1)`.

1. **Layer increments.** `e_0 = 0`, and `e_k <= k e_(k+1)` for `1 <= k <= n-1`.
2. **One-letter reduction.** With `n = m+d-1` and `c(m,d) = sum_(j=0)^(d-1) (n-1)!/(n-1-j)!`,

   `|S_(m+1,m+d+1) Y| - |Y| <= c(m,d) (|X_n Y| - |Y|)`.

   For example `c(m,2) = m+1`, so `|X_1 X_2 Y| <= 2|X_2 Y| - |Y|` (`P_(2,1)`) and
   `|X_2 X_3 Y| <= 3|X_3 Y| - 2|Y|` (`P_(2,2)`). The sharper form of step 1 also gives
   `|X_2 X_3 Y| <= 3|X_3 Y| - |Y| - |X_1 Y|`.
3. **Consequences.**
   - (a) A finite `Y` with `|X_(m+d-1) Y| < (1 + 1/c(m,d)) |Y|` solves `P_(d,m)` by the
     cardinality method (item 3 of `thompson-f-nonamenable-iff-some-monomial-set-doubles`). For
     `P_(2,2)` the threshold is `|X_3 Y| < (4/3)|Y|`.
   - (b) If `S_(m+1,m+d+1)` is doubling, then `|X_(m+d-1) Y| >= (1 + 1/c(m,d))|Y|` for every
     finite `Y ⊆ M`. Every non-amenability proof through item 2 of the equivalence claim
     therefore yields an explicit Cheeger constant for some letter set `X_n` on `M`.
   - (c) In each degree `D`, `Λ_(X_n)(D) >= 1 + (Λ_S(D) - 1)/c(m,d)` and
     `Λ_S(D) <= c(m,d) Λ_(X_n)(D) - c(m,d) + 1`, in the notation of
     `thompson-f-monomial-doubling-ratio-is-a-finite-computation`.

**Data.**
- For `P_(2,1)` the bound `Λ_(S_(2,4))(D) <= 2 Λ_(X_2)(D) - 1` holds with equality for
  `D = 1, ..., 10` on the main-branch exact tables (`7/2 = 2·9/4 - 1`, `45/17 = 2·31/17 - 1`,
  ...). The same optimal sets attain both. It is strict at `D = 11, 12`.
- For `P_(2,2)` the bound is far from tight: at `D = 11`, `3 Λ_(X_3)(11) - 2 ≈ 3.24`, while
  `Λ_(S_(3,5))(11) ≈ 2.72`.
- `experiments/thompson-f-2026-09-17/layer_increment_check.py` tests items 1 and 2 on 400 random
  sets and on the optimal `X_2` sets. There are 0 violations, and `e_1 = e_2` is attained on
  the optimal set of degree 5.

**Scope.** Item 3(a) is a sufficient condition that is strictly stronger than solving
`P_(d,m)`. It turns the target into one explicit letter set with an explicit threshold, but it
proves nothing about whether that threshold is reachable.
