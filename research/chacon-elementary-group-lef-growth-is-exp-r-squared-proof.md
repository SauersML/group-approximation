---
rg: 2
id: chacon-elementary-group-lef-growth-is-exp-r-squared-proof
kind: route
title: One pattern occurrence per level-(n+1) block from the slot pair (0,1), then the short-tower bound; linear recurrence above
target: chacon-elementary-group-lef-growth-is-exp-r-squared
requires: [short-towers-force-large-lef-models, subshift-elementary-group-lef-growth-complexity-bounds]
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part4.md]
---

1. **Slots.** In B_M the level-n slot sequence is 0, 1, s_1, 0, 1, s_2, …, so the pair (0,1) occurs once per B_{n+1}-copy (Lemma Ch0).
2. **Local characterization.** In B_M, y_c = y_{c+1} = 0 and y_{c+h_n+1} = 1 exactly when c ends a copy followed by the slots (0,1).
   - If c has offset o ≤ h_n − 2, the letter at c + h_n + 1 repeats y_{c+1} or y_c, which is 0.
   - If o = h_n − 1, y_{c+1} = 0 forces slot 0, and c + h_n + 1 is the next slot.
3. **No returns.** Two occurrences sit at the same offset in distinct B_{n+1}-copies, so they are ≥ h_{n+1} apart.
4. **Cost.** e_{W_n} = e_0·u^{-1}e_0u·u^{-(h_n+1)}e_1u^{h_n+1}. Two nested commutators and the Whitehead conjugations give ≤ 154 + 48h_n.
5. **Lower bound.** For m ≥ 2 take n least with h_{n+1} > 2m, so h_n ≤ 2m and κ ≤ 154 + 96m. The short-tower bound applies at r ≥ 3080 + 2400m.
6. **Upper bound.**
   - Words of length n ≤ h_k lie in B_k s B_k ⊆ B_{k+1}, and windows of length 2h_{k+1} + 1 contain a B_{k+1}-copy. So R(n) < 18n + 9.
   - Theorem A(c) gives N(n) ≤ 2R(n), and L(r) < 2^{9N(4r+1)²}.
