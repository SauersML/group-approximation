---
rg: 2
id: one-hole-toeplitz-lef-growth-at-least-exp-r-squared-proof
kind: route
title: Take the least period above 2m and apply the short-tower bound
target: one-hole-toeplitz-lef-growth-at-least-exp-r-squared
requires: [one-hole-toeplitz-subshifts-have-linear-cost-towers, short-towers-force-large-lef-models]
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part2.md]
---

1. For m ≥ 1 let k be least with p_k > 2m. Then p_{k−1} ≤ 2m, so p_k ≤ 2ρm.
2. W_k has no returns 0 < |t| ≤ 2m, and κ ≤ |A|(5 + 48·2ρm).
3. The short-tower bound gives L_X(r) ≥ 2^{d(d−1)/2} ≥ 2^{18m²} (d = 6m+3) for r ≥ 20κ + 480m. This holds whenever r ≥ 100|A| + (1920ρ|A| + 480)m.
4. Take m = ⌊(r − 100|A|)/(1920ρ|A| + 480)⌋ ≥ 1.

Details: artifact part 2, Theorem T2.
