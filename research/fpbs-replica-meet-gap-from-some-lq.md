---
rg: 2
id: fpbs-replica-meet-gap-from-some-lq
kind: route
title: A finite mean of the k-fold infinite-cluster intersection above p_c forces the full k-fold meet to be almost surely finite there
target: fpbs-replica-meet-threshold-gap-universal
requires:
  - fpbs-two-point-some-lq-above-pc-universal
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md
---

1. [Q_fin] supplies `p > p_c` and `k` with
   `E|K^1_inf(o) ∩ ... ∩ K^k_inf(o)| < infinity`. So that intersection is a.s.
   finite.
2. On `{|M_k(o)| = infinity}`, every `K^i(o)` is infinite, so
   `M_k(o) = ∩_i K^i_inf(o)`.
3. Hence `|M_k(o)| < infinity` a.s. at `p`, which is [cap_fin].
