---
rg: 2
id: chacon-elementary-group-lef-growth-is-exp-r-squared
kind: claim
title: For the weakly mixing Chacón subshift, EL_3(LC(X,F_2)⋊Z) has LEF growth exp(Θ(r²)), through three-letter towers {y_0 = y_1 = 0, y_{h_n+1} = 1}
distinct_from:
  sturmian-elementary-group-lef-growth-is-exp-r-squared: that uses an irrational rotation factor; Chacón has no eigenvalues, and the towers come from its rank-one block structure.
  thue-morse-elementary-group-lef-growth-is-exp-r-squared: that uses a Toeplitz factor; Chacón has none.
---

**Statement.** Let X_Ch be the Chacón subshift (B_{n+1} = B_n B_n 1 B_n, h_{n+1} = 3h_n + 1).
- For n ≥ 1, W_n = {y_0 = 0, y_1 = 0, y_{h_n+1} = 1} is nonempty, has no returns 0 < |t| < h_{n+1}, and |e_ij(e_{W_n})| ≤ 154 + 48h_n.
- So the LEF growth of G = EL_3(LC(X_Ch,F_2)⋊Z) satisfies:
  - 2^{18((r − 3080)/2400 − 1)²} ≤ L(r) for r ≥ 7880;
  - L(r) < 2^{9(144r+54)²} for all r.

**Why it matters for the open question.** Chacón is weakly mixing, so none of the rotation or Toeplitz factor arguments apply. The same letter-change mechanism at the partial-rigidity times h_n still gives linear-cost towers.

**Status: established** by `chacon-elementary-group-lef-growth-is-exp-r-squared-proof`. UNREVIEWED; queued with sk-verify-7.
