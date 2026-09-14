---
rg: 2
id: thue-morse-elementary-group-lef-growth-is-exp-r-squared-proof
kind: route
title: Period-doubling factor plus one-hole Toeplitz towers below; linear recurrence and periodic models above
target: thue-morse-elementary-group-lef-growth-is-exp-r-squared
requires: [lef-growth-of-subshift-el-groups-is-monotone-under-factors, one-hole-toeplitz-lef-growth-at-least-exp-r-squared, subshift-elementary-group-lef-growth-complexity-bounds]
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part3.md]
---

1. **Factor.** Put q_n = 1 + t_n + t_{n+1}. Then q_{2n} = 0 and q_{2n+1} = 1 + q_n, so q is the period-doubling fixed point. The block map therefore maps X_TM onto X_PD (artifact part 3, Lemma TM1).
2. **Toeplitz.** The period-doubling sequence has the single hole class 2^k − 1 mod 2^k, and X_PD is infinite and minimal (Lemma TM2).
3. **Lower bound.** The one-hole Toeplitz bound gives L_{X_PD} ≽ exp(r²), and factor monotonicity passes it to X_TM.
4. **Linear recurrence.**
   - Words of length n ≤ 2^k lie in σ^{k+1}(ab).
   - σ³(0) and σ³(1) contain all four two-letter words, so σ^{k+4}(c) contains every n-word.
   - Any window of length 2^{k+5} < 64n contains such a block (Lemma TM3).
5. **Upper bound.** Theorem A(c) of the required complexity-bounds claim: N(n) ≤ 2R(n) ≤ 128n, so L(r) < 2^{9N(4r+1)²}.
