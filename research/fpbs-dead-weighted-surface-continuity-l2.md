---
rg: 2
id: fpbs-dead-weighted-surface-continuity-l2
kind: route
title: Reach critical l2 on every generating set by an open-closed continuity argument along per-generator weights from a known anchor
target: fpbs-critical-dyadic-projection-estimate
requires:
  - fpbs-one-edge-sprinkling-l2-lipschitz
  - fpbs-uniform-floor-equivalence-restricted-to-monotone-paths
---

**Dead.** The route puts every generating set `S` of `Gamma` on one weighted
Cayley graph with generators `U ⊇ S ∪ S_0`. It connects a known critical-l2
anchor, such as a product or nonunimodular generating set, to the uniform point
`p_c(S) 1_S` by a path of critical weights, and argues open-closed.

* **Openness holds** with explicit radius:
  `fpbs-one-edge-sprinkling-l2-lipschitz`.
* **It dies at closedness.** Closedness needs `inf phi > 0` along the path.
  That floor already implies the conclusion at the endpoint, and on monotone
  paths it is equivalent to it
  (`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`, OPEN after
  referees refuted the "every path" form on 2026-09-17).
* **What survives** is a one-step certificate. It needs an explicit anchor norm
  above the sprinkling cost, and qualitative anchor theorems supply none.
* **Calibration.** The explicit tree anchor certifies `T_{2k} x Z` for `k >= 4`.
  It certifies `F_2 x Z` only if `p_c(T_4 x Z) < 0.21085`.
