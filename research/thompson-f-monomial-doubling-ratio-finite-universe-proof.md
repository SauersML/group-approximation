---
rg: 2
id: thompson-f-monomial-doubling-ratio-finite-universe-proof
kind: route
title: Letters above R_S(D) are never passed, so the optimal expansion ratio in degree D lives in M_(D, R_S(D))
target: thompson-f-monomial-doubling-ratio-is-a-finite-computation
requires:
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
artifacts:
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
---

Notation follows the claim. The route requires the equivalence claim only for the definition
of "doubling" and for item 3 of that claim.

**Left multiplication by one letter.** For a normal form `w = x_(w_1) ... x_(w_n)`, the
relations `x_j x_i = x_i x_(j+1)` (`i < j`) give the normal form of `x_j w` as follows. Scan
`k = 1, 2, ...` while `w_k < j`, replacing `j` by `j + 1` at each step, then insert the final
`j` before the first unscanned letter. Every scanned ("passed") letter is smaller than the
inserted letter, and the inserted letter is at most `j + n`.

**Lemma A (inert letters).** Let `s = x_(s_1) ... x_(s_d) ∈ S` and `w ∈ M_D`. Put
`R = R_S(D)`, and write `w = a b` with `a` the letters `<= R` and `b` the letters `> R`.
Then `s w = (s a) b`, and all letters of `s a` are `<= R`.
- *Proof.* `s w = x_(s_1)(... (x_(s_d) w))`. The letter `x_(s_t)` acts on a word of length
  `D + d - t`, so its inserted letter is at most `s_t + D + d - t <= R`. Passed letters are
  smaller than the inserted letter, so no letter `> R` is ever passed. Each inserted letter
  is `<= R`, so it lands before `b`. Inducting over `t = d, d-1, ..., 1` gives the claim.

**Lower bound.** Let `Y ⊆ M_D` be finite and nonempty. Group `Y` by the suffix `b`:
`Y = ⊔_b Y_b b` with `Y_b ⊆ M_(j,R)`, `j = D - |b|`. By Lemma A, `S Y = ⊔_b (S Y_b) b`. These
pieces are disjoint because `b` is recovered as the letters `> R` of any element. Hence
`|S Y| / |Y| >= min_b |S Y_b| / |Y_b| >= min_(0 <= j <= D) λ*(j, R)`, where `λ*(j, L)` is the
minimum of `|S Z| / |Z|` over nonempty `Z ⊆ M_(j,L)`.

**The minimum is attained at `j = D`.** Let `j < D` and `Z ⊆ M_(j,R)`, and put
`b = x_R^(D-j)`, the letter `R` repeated `D - j` times.
- *`b` is inert for `Z`.* For `z ∈ M_j`, the letters inserted in computing `s z` are at most
  `R_S(j) = R - (D - j) < R`. So letters equal to `R` are never passed, the inserted letters
  land before them, and `s (z b) = (s z) b`.
- *The embedding.* Also `z b` is a normal form in `M_(D,R)`, and `z -> z b` is injective, so
  `|S (Z b)| / |Z b| = |S Z| / |Z|`.
- *Conclusion.* `λ*(D, R) <= λ*(j, R)`, so `min_j λ*(j, R) = λ*(D, R)`. Together with the
  lower bound and the trivial `λ*(D, R) >= Λ_S(D)`, this proves item 1.

**Item 2.** Append one letter `N > R_S(D)` to every word of `Y ⊆ M_D`. By Lemma A this
preserves `|S Y| / |Y|` and lands in `M_(D+1)`.

**Item 3.** Since `S` is homogeneous, `S Y_D ⊆ M_(D+d)` for the degree-`D` part `Y_D` of `Y`,
and these parts are disjoint across `D`. So `|S Y| < 2|Y|` forces `|S Y_D| < 2|Y_D|` for some `D`.
Conversely a finite `Y ⊆ M_D` with ratio `< 2` exists iff `Λ_S(D) < 2`, by item 1. The
common right multiple comes from item 3 of the equivalence claim with `u, v ∈ K[Y] ⊆ K[M_D]`.

**Computation.**
- *The network.* For a universe `U = M_(D,L)`, the network `source -K-> y -∞-> s y -J-> sink`
  has minimum cut `min_Y (K(|U| - |Y|) + J |S Y|)`, because the infinite edges force the
  neighbors of the source side onto the source side.
- *Iteration.* Hence `max_Y (K|Y| - J|S Y|) = K|U| - maxflow`, and the source side of a
  minimum cut attains it. With `K/J` the current best ratio, a positive value yields a
  strictly better `Y`. The program recounts `|S Y|` directly and aborts if that fails. A
  zero value certifies optimality.
- *Checks.* `experiments/thompson-f/doubling_check.py` compares the result with an exhaustive
  subset search on all universes with at most 15 elements. It also confirms item 1
  numerically: `λ*(D, L)` is constant for `R_S(D) <= L <= R_S(D) + 4` and `D <= 6`, for four
  sets `S`.
