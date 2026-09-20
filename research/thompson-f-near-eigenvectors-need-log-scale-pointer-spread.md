---
rg: 2
id: thompson-f-near-eigenvectors-need-log-scale-pointer-spread
kind: claim
title: A unit nonnegative vector on one-sided pointed forests of Thompson's F with Rayleigh value 4 - delta has P(min(s,r) <= 2^J) <= 6(J+1) sqrt(delta) for its pointer size s and neighbour size r, so every vector class with bounded pointer trees is capped below 1 and Foelner-type vectors must live at log-scale at least 1/(12 sqrt(delta))
distinct_from:
  thompson-f-product-forest-vectors-stay-below-71-72: that caps one amplitude class (product form) at 71/72 and records the comonotone condition on pointer and neighbour sizes as "not proved in the graph ... a heuristic only"; this proves that condition, in the stronger form P(s <= t < s+r) <= 2 sqrt(delta), for every amplitude, and derives the log-scale law from it.
  thompson-f-one-sided-forest-windows-are-norm-lossless: that proves the support R costs nothing and that near-eigenvectors put vanishing mass on pointer-leaf states (the scale t = 1); this extends the leaf statement to every dyadic scale 2^j at cost 6 sqrt(delta) per scale, and it caps every vector with bounded pointer trees, which the deficiency identity does not.
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that is a numerical saturation for one correlated amplitude class; this is a necessary condition on all near-eigenvectors, with no ceiling for any class whose pointer and neighbour sizes escape to infinity.
  thompson-f-iid-forest-test-vectors-are-bounded-below-one: that bounds i.i.d. product vectors by 1 - 1/1280 for every truncation; this bounds all vectors with pointer trees of at most N leaves by 1 - 1/(144 (ceil(log2 N) + 1)^2), which depends on N but not on the amplitudes.
  thompson-f-is-amenable: that is the open root; this is a necessary condition on its Kesten witnesses and decides nothing.
artifacts:
  - experiments/thompson-f-log-scale-spread-2026-09-17/spread_check.py
  - experiments/thompson-f-log-scale-spread-2026-09-17/spread_check_n9.out
---

**ESTABLISHED** (lane proof, not reviewed) by
`thompson-f-near-eigenvectors-need-log-scale-pointer-spread-proof`.

**Setting.** This uses the notation of `thompson-f-one-sided-forest-windows-are-norm-lossless`:
- `K = s_0 + s_0^{-1} + s_1 + s_1^{-1}`, so `||K|| = 4||P||`;
- `R` is the image of the positive monoid, the set of one-sided pointed forests `(T_0, T_1, ...; i)`;
- every vertex of `R` has a pointer-right move and a merge move, and both stay in `R`.

For a state `x = (T_0, T_1, ...; i)` put:
- `s(x) = |T_i|`, the number of leaves of the pointer tree;
- `r(x) = |T_{i+1}|`, the number of leaves of its right neighbour (`1` if that tree is a leaf).

For `f ∈ l^2(F)` with `f ≥ 0`, `||f|| = 1` and `supp f ⊆ R`, write `μ = f^2`, a probability measure on
`R`, and `δ(f) = 4 − <f, K f>`.

**Theorem.** For every such `f`, with `δ = δ(f)`:
1. **(Merge at one scale.)** `μ(s ≤ t < s + r) ≤ 2√δ` for every real `t`.
2. **(Pointer right at one scale.)** `μ(r ≤ t) ≤ μ(s ≤ t) + 2√δ`, and hence `μ(r ≤ t < r + s) ≤ 4√δ`.
3. **(All dyadic scales.)** `μ(min(s, r) ≤ 2^J) ≤ 6(J + 1)√δ` for every integer `J ≥ 0`.

In particular `μ(s ≤ t < r) ≤ 2√δ` and `μ(r ≤ t < s) ≤ 4√δ`. This is the "comonotone" condition that
`thompson-f-product-forest-vectors-stay-below-71-72` records as a heuristic.

**Corollaries.**
- **(C1) Bounded-pointer class kill.** Suppose `μ(s ≤ N) ≥ c > 0`. Then
  `δ ≥ c^2 / (36 (⌈log_2 N⌉ + 1)^2)`.
  - If the support of `f` has only pointer trees with at most `N` leaves, then `c = 1`, and
    `<f, K f> ≤ 4 − 1/(36 (⌈log_2 N⌉ + 1)^2)`.
  - This holds for every amplitude, signed ones included, because `|f|` does at least as well as `f`.
    So no vector supported there certifies more than `||P|| ≥ 1 − 1/(144 (⌈log_2 N⌉ + 1)^2)`.
  - It also covers every truncated window ansatz (tree sizes `≤ N`), whatever the correlations between
    trees.
- **(C2) The log-scale law of a Kesten witness.** Let `δ ≤ 1/144` and put `J_δ = ⌊1/(12√δ)⌋ − 1 ≥ 0`.
  Then
  `μ(min(s, r) ≤ 2^{J_δ}) ≤ 1/2`. So the median of `log_2 min(s, r)` is at least `1/(12√δ) − 2`.
  - `F` is amenable iff there are unit `f ≥ 0` on `R` with `δ(f) → 0`
    (`thompson-f-one-sided-forest-windows-are-norm-lossless`, item 2).
  - Every such sequence has pointer and neighbour sizes of order at least `2^{c/√δ}`, and
    `min(s, r) → ∞` in `μ`-probability.
  - The laws of `s`, `s + r` and `r` are within `2√δ` of one another, one-sidedly, at every
    threshold.

**Class killed (C1).**
- *The class:* vectors on `R` whose pointer tree has at most `N` leaves on a set of mass `≥ c`. Any
  amplitudes are allowed.
- *Invariant:* the law of `log_2 min(s, r)` under `f^2`.
- *Dying step:* the merge and pointer-right edges. At each dyadic scale `2^j`, they allow only
  `6√δ` of mass with `min(s, r)` crossing that scale. A mass `c` stuck below `N` must cross one of
  `⌈log_2 N⌉ + 1` scales, which forces `δ ≥ c^2 / (36 (⌈log_2 N⌉ + 1)^2)`.

**Scope.**
- This is a necessary condition only. It says nothing about `||P||`.
- The log-scale continuum of `thompson-f-norm-bound-from-log-scale-forest-limit` already sends sizes
  to infinity, and so do the Markov families. So this caps neither of them.
- It tells a certificate designer that the truncation must grow like `N ≥ 2^{c/√δ}` to reach
  Rayleigh value `4 − δ`.

Proof route: `thompson-f-near-eigenvectors-need-log-scale-pointer-spread-proof`.
