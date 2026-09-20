---
rg: 2
id: hadamard-gadget-ratio-below-two-at-k6
kind: claim
title: Exactly, delta_6 = 194052011567061629/2^59 < 16/47, so R*(6) <= 1.98884 < 2 and R*'(6) <= 1.98123 < 2 - no Hadamard Had_k -> Max-2Lin(2) gadget with k <= 6 (arity at most 64) crosses the padding line, and any witness for hadamard-gadget-crosses-padding-line needs k >= 7
distinct_from:
  hadamard-gadget-deletion-ratio-window: that proves the decoder bound R*(k) <= 1 + delta_k (3 - 2^(2-k)) and evaluates delta_k exactly only for k <= 5, leaving k = 6 as a Monte Carlo estimate; this evaluates delta_6 exactly by a new affine-class split and turns the estimate into a proof.
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2 for some k; this rules out k = 6, the last arity at which the nearest-codeword decoder adversary wins.
  hadamard-gadget-ratio-k4-sandwich: that improves the k = 4 upper bound by an LP adversary mixture; this is the decoder adversary at k = 6, where no LP is feasible.
artifacts:
  - experiments/ugc-hadamard-k6-exact-2026-09-17/rm1_six_exact.c
  - experiments/ugc-hadamard-k6-exact-2026-09-17/k6_full_run.log
  - experiments/ugc-hadamard-k6-exact-2026-09-17/k5_validation.log
  - experiments/ugc-hadamard-k6-exact-2026-09-17/results-2026-09-19.txt
---

**ESTABLISHED.** Proof: `hadamard-gadget-ratio-below-two-at-k6-proof`. It
combines item 3 of `hadamard-gadget-deletion-ratio-window` (ESTABLISHED) with
one exact integer enumeration, validated against every earlier exact value.

## Statement

The notation is that of `hadamard-gadget-deletion-ratio-window`.

1. **Exact mean distance to RM(1,6).** For uniform `xi in {-1,1}^64`,
   * `E max_i |W_i| = 6027415333417607360 / 2^58 = 20.9117977566...`;
   * `delta_6 = 194052011567061629 / 2^59 = 0.33662658002...`.
2. **Parity identity (all k >= 2).** `E max_i |W'_i| = E max_i |W_i|`, where
   `W'_i = W_i - xi_0` is the punctured spectrum. Equivalently
   `delta'_k = 1/2 - K(1 - 2 delta_k) / (2(K - 1))`, so `delta'_k < delta_k`.
   At `k = 6` this gives `delta'_6 = 0.33403335...`.
3. **Class kill at k = 6.** The kill threshold is `1/(3 - 4/64) = 16/47 = 0.3404255...`,
   and `delta_6` sits below it by `0.0037990`. Hence
   * `R*(6) <= 1 + (47/16) delta_6 = 18343816580506672371 / 2^63 = 1.98884057... < 2`;
   * `R*'(6) <= 1 + (47/16) delta'_6 = 1.98122297... < 2`.

So no `(c, s)`-gadget reducing Max-`Had_6` (HHM+15 Definition 2.24), or
generic Max-`Had'_6`, to Max-2Lin(2) has `s/c >= 1.98885`.

* **Joined with item 4 of the window node.** Every Hadamard gadget of arity
  at most `64` has deletion ratio at most `1.98885`, bounded away from `2`.
* **Joined with the growth of delta_k.** The decoded threshold adversary is
  exhausted exactly here. Its value `1 + delta_k (3 - 4/K)` is `1.9888` at
  `k = 6` and about `2.1117` at `k = 7` (Monte Carlo, `delta_7 ~ 0.37446`).
  So `k = 7` is the first open arity, and it needs a new adversary.

## What this changes

* `hadamard-gadget-crosses-padding-line` moves from "`k >= 6`" to
  "`k >= 7`". This is the first arity at which the witness must beat
  something other than nearest-codeword decoding.
* The claim that the decoder adversary wins at `k = 6` had rested on one
  Monte Carlo run (`20.9110 +- 0.0007`). The exact value `20.91180` lies
  1.2 standard errors from it, and the margin to the threshold `20.4255`
  is `0.486`, which is large.
* Any Hadamard-gadget crossing of the padding line has to meet all of the
  following:
  * arity at least `128`;
  * true soundness, which is not relaxable;
  * `s/c < 5/2 - 2^(-6)`;
  * a positive folding gap, `eta_k > R*(k) - 2`.
