---
rg: 2
id: fpbs-bs-via-replica-meet-threshold
kind: route
title: If k independent clusters meet finitely at some p above p_c then p is below p_u, because above p_u the unique infinite clusters meet in an infinite invariant set
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-replica-meet-threshold-gap-universal
  - fpbs-replica-meet-threshold-sandwich
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md
---

1. [cap_fin] supplies `p > p_c` and `k` such that `M_k(o)` is a.s. finite at
   `p`. So `p_cap^(k) >= p > p_c`.
2. Item 3 of `fpbs-replica-meet-threshold-sandwich` gives `p_u >= p_cap^(k)`.
3. Hence `p_u > p_c`.

**Load-bearing premise.** Only [cap_fin].
