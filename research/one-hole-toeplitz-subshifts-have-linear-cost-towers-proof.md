---
rg: 2
id: one-hole-toeplitz-subshifts-have-linear-cost-towers-proof
kind: route
title: Returns are realized on the dense orbit, and both return positions must be the hole
target: one-hole-toeplitz-subshifts-have-linear-cost-towers
requires: []
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part2.md]
---

1. **Cost.** W_k is the disjoint union over letters a of {y_0 = a, y_{p_k} ≠ a}. Each piece has indicator e_a + e_a u^{-p_k} e_a u^{p_k}, whose transvection costs ≤ 5 + 48p_k by one commutator and the Whitehead conjugations.
2. **Nonempty.** If W_k = ∅, every point of X is p_k-periodic, so X is finite.
3. **No returns.**
   - y ∈ W_k ∩ T^tW_k gives y_0 ≠ y_{p_k} and y_{−t} ≠ y_{−t+p_k}.
   - The mismatch set of y lies in one residue class mod p_k. For a two-sided point this follows from the hypothesis on the Toeplitz point by passing windows to limits.
   - So t ≡ 0 mod p_k.

Details: artifact part 2, Theorem T1.
