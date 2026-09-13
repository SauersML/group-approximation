---
rg: 2
id: elementary-groups-over-polynomial-s-integers-are-fp
kind: claim
title: E_n(Z[1/m][t_1..t_k]) is finitely presented for n >= k+4
distinct_from:
  steinberg-finite-presentation-and-kazhdan-theorem: that is Krstić–McCool's finite presentation of the Steinberg group St_n(R) with property (T), and it draws no conclusion for EL_n(R); this controls the kernel K_2(n,R) for polynomial rings over Z[1/m] in the stable range, so the elementary group itself is finitely presented.
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`elementary-groups-over-polynomial-s-integers-are-fp-proof`. It imports K-theory
from textbooks, as listed in the route. Not independently reviewed.

**Statement.** Let `m >= 1`, `k >= 0`, `A = Z[1/m]`, `R = A[t_1,...,t_k]` and
`n >= k+4`. Then `E_n(R)` is finitely presented.

**Special case.** `E_5(Z[t])` is finitely presented, with
`K_2(5, Z[t]) = K_2(Z) = Z/2`.

**Compare.**
- Krstić–McCool: `SL_3(Z[t])` is not finitely presented.
- Bux–Mohammadi–Wortman, arXiv:0801.1332, Thm 1: `SL_n(Z[t])` is not of type
  `FP_(n-1)`.

Neither excludes finite presentation for `n >= 5`. This statement is very likely
known to experts. No novelty is claimed.
