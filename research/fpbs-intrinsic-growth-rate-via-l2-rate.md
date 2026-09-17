---
rg: 2
id: fpbs-intrinsic-growth-rate-via-l2-rate
kind: route
title: The l2 rate is dominated by the l1 rate through the Schur row-sum bound
target: fpbs-intrinsic-growth-rate-positive-at-pu
requires:
  - fpbs-intrinsic-l2-rate-closed-zero-set
  - fpbs-intrinsic-l2-rate-bounded-below-above-pu
---

Complete route. By item 1 of `fpbs-intrinsic-l2-rate-closed-zero-set`,
`Lambda(t) <= lambda_1(t)`. The reason is the bound
`||T^(R)_t||_(2->2) <= ||f^(R)_t||_1 = E_t|B^int_R(o)|`, stated as (K2) in its
proof. So `Lambda(p_u) > 0`, from
`fpbs-intrinsic-l2-rate-bounded-below-above-pu`, gives `lambda_1(p_u) > 0`.
