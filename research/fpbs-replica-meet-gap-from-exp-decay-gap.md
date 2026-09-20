---
rg: 2
id: fpbs-replica-meet-gap-from-exp-decay-gap
kind: route
title: Uniform exponential decay just above p_c makes a high replica moment finite, so the replica meet is almost surely finite there
target: fpbs-replica-meet-threshold-gap-universal
requires:
  - fpbs-pc-below-exp-decay-threshold-universal
  - fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

This is Corollary 3 of the artifact.

1. Take `p` in `(p_c, p_exp)` from `fpbs-pc-below-exp-decay-threshold-universal`,
   so `xi_p > 0`.
2. Choose `k > gr(G)/xi_p`. Item 1 of
   `fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold` gives
   `Z_k(p) = E|M_k(o)| < infinity`.
3. So `|M_k(o)| < infinity` a.s. at `p > p_c`. That is `p_c < p_cap^(k)`,
   which is the target.
