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
2. **Nonempty.** If W_k = ∅, then x_s = x_{s+p_k} for all s, so x is periodic.
3. **No returns.**
   - W_k ∩ T^tW_k is open, so if it is nonempty it contains an orbit point T^s x.
   - Then x_s ≠ x_{s+p_k} and x_{s−t} ≠ x_{s−t+p_k}. So s and s − t are not in Per_{p_k}(x), hence both lie in the single hole class.
   - So t ≡ 0 mod p_k.

Details: artifact part 2, Theorem T1.
