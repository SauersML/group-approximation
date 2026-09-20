---
rg: 2
id: hadamard-gadget-ratio-is-below-two-at-k6-proof
kind: route
title: Exact binomial moments of the Walsh exceedance counts plus a rationally verified moment-LP dual, summed over even thresholds, bound delta_k from above
target: hadamard-gadget-ratio-is-below-two-at-k6
requires: [hadamard-gadget-deletion-ratio-window]
artifacts:
  - experiments/ugc-hadamard-limit-2026-09-17/delta_exact_certificate.py
  - experiments/ugc-hadamard-limit-2026-09-17/delta_exact_k6_M4.log
  - experiments/ugc-hadamard-limit-2026-09-17/delta_exact_k7_M3.log
---

1. **Reduction to `delta_k`.** Item 3 of `hadamard-gadget-deletion-ratio-window`
   is the decoded threshold adversary with a uniformly random nearest
   codeword. It gives `R*(k) <= 1 + delta_k (3 - 4/K)`, with
   `delta_k = 1/2 - E max|W| / (2K)`. The right side increases in `delta_k`,
   so a lower bound on `E max|W|` suffices.
2. **Layer cake.** Each `W(a)` is a sum of `K` signs and so is even. Hence
   `E max|W| = sum_{t = 2, 4, ..., K} 2 Pr[N_t >= 1]`, where
   `N_t = #{a : |W(a)| >= t}`, an integer in `[0, K]`.
3. **Exact moments.** For `r <= M` define
   `S_r(t) = E C(N_t, r) = sum over r-sets {a_l} of Pr[min_l |W(a_l)| >= t]`.
   * Group the points `i` by the pattern `v = (a_l . i)_l`. The group sums
     `s_v` are independent sums of `c_v` signs, and
     `W(a_l) = sum_v (-1)^(v_l) s_v`. So the joint law depends only on the
     multiset `{(v, c_v)}`, up to a relabelling of `l` that the event ignores.
   * The script enumerates all `C(K, r)` sets and buckets them by a canonical
     key. It asserts that the bucket sizes sum to `C(K, r)`.
   * At `k = 6` there are 2, 2, 3 and 5 keys for `r = 1, 2, 3, 4`.
   * For each key it builds the integer count law (out of `2^K`) by `K`
     shifted additions. The additions are done modulo primes below `2^20`
     whose product exceeds `2^(K+1)`, and the counts are recovered by CRT.
     The per-prime histogram sums are below `2^45`, so the float64 bincount
     used to form them is exact.
   * Every `S_r(t)` is thus an exact `Fraction`.
4. **Moment-LP dual.** Let `P(n) = y_0 + sum_{r=1..M} y_r C(n, r)` satisfy
   `P(n) <= 1[n >= 1]` for `n = 0..K`. Then
   `Pr[N_t >= 1] >= E P(N_t) = y_0 + sum_r y_r S_r(t)`. This is weak duality
   for `min sum_{j>=1} p_j` subject to `sum_j C(j, r) p_j = S_r(t)`,
   `sum_j p_j = 1` and `p >= 0`, which the law of `N_t` satisfies.
   * The script takes the float HiGHS equality duals, rounds them to
     rationals with denominator at most `10^12`, and lowers `y_0` by the
     exact maximum violation.
   * It then asserts the `K + 1` inequalities in exact arithmetic.
   * It evaluates the bound exactly and clips it at `0`.
5. **Result.**
   * `k = 6, M = 4`: `E max|W| >= 20.7364582`, so `delta_6 <= 0.3379964`.
     This is below `16/47` by `0.00243`, and
     `R*(6) <= 1.9928645`.
   * `k = 7, M = 3`: `delta_7 <= 0.3810677`, so `R*(7) <= 2.1312947`.
   * The exact rationals are in the logs.

**Why four moments.** At `k = 6` the bounds on `delta_6` are:

| moments | bound on `delta_6` |
|---|---|
| 2 (Dawson--Sankoff) | 0.34751 |
| 3 | 0.3458 |
| 4 | 0.33800 |

Only the four-moment bound is below `16/47`. The Monte Carlo value is
`0.33663`, so the remaining slack is about `0.0014`.
