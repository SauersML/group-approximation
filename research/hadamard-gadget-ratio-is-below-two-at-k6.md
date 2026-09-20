---
rg: 2
id: hadamard-gadget-ratio-is-below-two-at-k6
kind: claim
title: R*(6) <= 1.99287 < 2, so no Hadamard gadget of arity at most 64 crosses the padding line; also R*(7) <= 2.13130 -- by an exact-rational four-moment certificate on delta_6 <= 0.337997 < 16/47
distinct_from:
  hadamard-gadget-deletion-ratio-window: that proves R*(k) < 2 for k <= 5 with delta_k computed by exhaustive enumeration, and only Monte Carlo estimates delta_6 ~ 0.3366; this certifies delta_6 <= 0.337997 rigorously without enumerating 2^64 words, closing k = 6.
  hadamard-gadget-ratio-k4-sandwich: that is an LP-optimized adversary mixture at k = 4; this bounds the single decoded adversary at k = 6, 7 through moment LPs on the Walsh exceedance counts.
  hadamard-gadget-ratio-is-monotone-in-k: that compares levels; this bounds individual levels. Combined, R*(k) < 2 for every k <= 6.
artifacts:
  - experiments/ugc-hadamard-limit-2026-09-17/delta_exact_certificate.py
  - experiments/ugc-hadamard-limit-2026-09-17/delta_exact_k6_M4.log
  - experiments/ugc-hadamard-limit-2026-09-17/delta_exact_k7_M3.log
---

**ESTABLISHED** (route `hadamard-gadget-ratio-is-below-two-at-k6-proof`).

Let `f` be uniform on `{-1,1}^(F_2^k)`, `K = 2^k`, and
`W(a) = sum_i f(i) chi_a(i)`. Then
`delta_k = 1/2 - E max_a |W(a)| / (2K)`, as in
`hadamard-gadget-deletion-ratio-window`. The certified bounds are exact
rationals printed in the logs. They are shown here rounded up.

| k | moments | `delta_k <=` | `R*(k) <= 1 + delta_k (3 - 4/K)` | threshold for `R* < 2` | previous rigorous bound |
|---|---|---|---|---|---|
| 6 | 4 | 0.3379965 | **1.9928645** | `delta_6 < 16/47 = 0.3404255` | `5/2 - 1/32 = 2.46875` |
| 7 | 3 | 0.3810677 | 2.1312947 | `delta_7 < 32/95 = 0.3368421` | `5/2 - 1/64 = 2.484375` |

**Consequences.**

* `R*(6) < 2`. With `hadamard-gadget-ratio-is-monotone-in-k`, or directly
  with the window node for `k <= 5`, we get `R*(k) < 2` for every `k <= 6`.
* Any witness for `hadamard-gadget-crosses-padding-line` needs `k >= 7`,
  meaning arity at least `128`.
* At `k = 7` the ratio is at most `2.1313`. A `k = 7` witness therefore has
  margin at most `0.132` above the padding line.
* The `k = 7` decoded adversary cannot close `k = 7` even with every moment:
  its Monte Carlo value `delta_7 ~ 0.3745` is above `32/95`. Closing `k = 7`
  needs a different adversary.

**Cross-checks with the same script, all against exact values from the
window node.**

* `k = 3`, `M = 4`: `delta_3 <= 179/1024 = 0.1748`, against `11/64 = 0.1719`.
* `k = 4`, `M = 4`: `0.24255`, against `1961/8192 = 0.23938`.
* At `k = 6`, the floating-point LP and the rationally verified dual agree to
  `1e-12` at every threshold.
