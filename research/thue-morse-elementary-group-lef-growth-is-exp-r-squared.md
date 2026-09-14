---
rg: 2
id: thue-morse-elementary-group-lef-growth-is-exp-r-squared
kind: claim
title: The LEF growth of EL_3(LC(X_TM,F_2)⋊Z) for the Thue–Morse subshift is exp(Θ(r²))
distinct_from:
  sturmian-elementary-group-lef-growth-is-exp-r-squared: that is the Sturmian family, which has a rotation factor; Thue–Morse has no irrational eigenvalue, and the lower bound comes through its period-doubling factor.
---

**Statement.** Let X_TM be the Thue–Morse subshift. Then L_{X_TM} ≃ exp(r²):
- **below:** exp(c r²), through the factor map x ↦ (1 + x_n + x_{n+1})_n onto period doubling, a one-hole Toeplitz subshift;
- **above:** 2^{9·128²(4r+1)²}, from linear recurrence R(n) ≤ 64n.

**Status: established** by `thue-morse-elementary-group-lef-growth-is-exp-r-squared-proof`. UNREVIEWED; queued with sk-verify-7.
