---
rg: 2
id: fpbs-some-lq-from-lq-threshold-gap
kind: route
title: The l^q threshold gap at q = 3 is a finite integer exponent above p_c
target: fpbs-two-point-some-lq-above-pc-universal
requires:
  - fpbs-two-point-lq-threshold-gap-universal
  - fpbs-lq-two-point-infinite-cluster-reduction
artifacts:
  - research/artifacts/fpbs/docs/lq-infinite-cluster-reduction-2026-09-18.md
---

1. Apply [Q] with `q = 3`. This gives some `p > p_c` with `Z_3(p) < infinity`.
2. `Z^inf_3 <= Z_3`, which is item (A) of
   `fpbs-lq-two-point-infinite-cluster-reduction`.
3. By item (B), `Z^inf_3(p)` is the expected intersection of three independent
   infinite clusters of `o`, which is [Q_fin] with `k = 3`.
