---
rg: 2
id: fpbs-bs-via-worst-pair-connectivity-rate
kind: route
title: An exponentially rare worst connection above p_c rules out uniqueness because uniqueness pins every connection above theta squared
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-worst-pair-connectivity-rate-positive-above-pc-universal
  - fpbs-worst-pair-connectivity-rate-kernel
---

**The route.**

1. Kernel (K) supplies `p > p_c` with `gamma(p) > 0`.
2. By item 2 of `fpbs-worst-pair-connectivity-rate-kernel`, no `p' <= p` has
   a unique infinite cluster. The reason: uniqueness gives
   `tau >= theta^2`, hence `gamma = 0`, while `gamma` is nonincreasing.
3. So `p_u >= p > p_c`.

**Load-bearing premise.** Only (K). The implication is established with Harris-FKG
and Fekete. This route dominates `fpbs-bs-via-sphere-two-point-rate`, because
(G) implies (K) (item 4), and it keeps the tree range `[1/sqrt(d-1),1)` that (G) misses.
