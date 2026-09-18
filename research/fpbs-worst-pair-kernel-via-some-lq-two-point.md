---
rg: 2
id: fpbs-worst-pair-kernel-via-some-lq-two-point
kind: route
title: One finite l^q exponent of the two-point function at one supercritical p forces the worst-pair rate log(gr)/q by Chebyshev on balls
target: fpbs-worst-pair-connectivity-rate-positive-above-pc-universal
requires:
  - fpbs-two-point-some-lq-above-pc-universal
  - fpbs-lq-two-point-infinite-cluster-reduction
artifacts:
  - research/artifacts/fpbs/docs/lq-infinite-cluster-reduction-2026-09-18.md
---

1. [Q_fin] gives some `p > p_c` and integer `k` with finite expected
   intersection of `k` independent infinite clusters.
2. By items (A) and (B) of `fpbs-lq-two-point-infinite-cluster-reduction`, this
   says exactly that `Z_k(p) < infinity`.
3. By item (C) of the same claim, `gamma(p) >= log(gr)/k > 0`. This is (K).
