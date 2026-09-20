---
rg: 2
id: fpbs-pc-below-exp-threshold-from-meet-gap-and-limit
kind: route
title: If the meet limit equals p_exp, a finite replica meet above p_c pushes p_exp above p_c
target: fpbs-pc-below-exp-decay-threshold-universal
requires:
  - fpbs-replica-meet-threshold-gap-universal
  - fpbs-replica-meet-limit-equals-exp-decay-threshold
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

This is the converse half of the equivalence in Section 4 of the artifact.

1. `fpbs-replica-meet-threshold-gap-universal` gives some `k` with
   `p_c < p_cap^(k)`, so `p_c < p_cap^(infty)`.
2. `fpbs-replica-meet-limit-equals-exp-decay-threshold` gives
   `p_cap^(infty) = p_exp`.
3. So `p_c < p_exp`.

Together with `fpbs-replica-meet-gap-from-exp-decay-gap`, this shows that,
granted the limit conjecture, the meet gap and Hutchcroft's Conjecture 2.1 are
equivalent.
