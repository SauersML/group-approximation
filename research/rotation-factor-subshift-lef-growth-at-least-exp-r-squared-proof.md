---
rg: 2
id: rotation-factor-subshift-lef-growth-at-least-exp-r-squared-proof
kind: route
title: Linear-cost towers at every scale fed into the short-tower bound
target: rotation-factor-subshift-lef-growth-at-least-exp-r-squared
requires: [rotation-factor-subshifts-have-linear-cost-towers, short-towers-force-large-lef-models]
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part1.md]
---

1. **Choice of W.** For m ≥ m_0, let n be largest with q_n ≤ 2m. Then n ≥ n_0 and q_{n+1} > 2m. So W = {x_0 = a, x_{q_n} ≠ a} has no returns 0 < |t| ≤ 2m, and κ ≤ 5 + 48q_n ≤ 5 + 96m.
2. **Short-tower bound.** With d = 6m + 3, L_X(r) ≥ 2^{d(d−1)/2} ≥ 2^{18m²} for r ≥ 20κ + 480m, and in particular for r ≥ 100 + 2400m.
3. **Choice of m.** Take m = ⌊(r − 100)/2400⌋. This is ≥ m_0 when r ≥ 100 + 2400·m_0, and m ≥ (r − 2500)/2400.

Details: artifact part 1, Theorem R2.
