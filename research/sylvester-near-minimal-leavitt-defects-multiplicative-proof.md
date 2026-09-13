---
rg: 2
id: sylvester-near-minimal-leavitt-defects-multiplicative-proof
kind: route
title: Exact globality makes the range and kernel compressions at a disjoint defect product fixed-point-free, and the triangular count pins the product
target: sylvester-near-minimal-leavitt-defects-are-multiplicative
requires:
  - sylvester-leavitt-kazhdan-fixed-ideals-are-global
  - sylvester-rank-functions-compress-to-commuting-kernels
  - sylvester-rank-functions-descend-to-quotients-and-compressions
  - sylvester-leavitt-defect-gap-and-geometric-descent
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

## Why sufficient

Artifact Section 3. Put `psi = rho_omega`, `P = D_(A_1) ... D_(A_k)`, `B = A_(k+1)` and
`T = iota_B(D_1000) = D_(B1000)`. `iota_B(F_2[R^x])` commutes with `P`, and `0 < f(k) <= 1/2` by
`sylvester-leavitt-defect-gap-and-geometric-descent`.

1. **Range corner.** `tau(A) = psi(iota_B(A) P) / f(k)` is a rank function
   (`sylvester-rank-functions-descend-to-quotients-and-compressions`). `tau(X Z) = tau(Z)` by
   `sylvester-leavitt-kazhdan-fixed-ideals-are-global` applied to `iota_B(Z) P`. So
   `f(k+1)/f(k) = tau(D_1000) >= c_*^Syl`.
2. **Kernel corner.** `sigma(A) = (psi([P_n; iota_B(A)]) - n f(k)) / (1 - f(k))` is a rank function
   (`sylvester-rank-functions-compress-to-commuting-kernels`). Globality gives
   `psi([P_n; iota_B(Z)]) = psi(iota_B(X) [P_n; iota_B(Z)]) <= psi([P_n; iota_B(X Z)])`. So `sigma` is
   fixed-point-free, and `psi([P; T]) >= f(k) + c_*^Syl (1 - f(k))`.
3. **Count.** The triangular count for the commuting `P` and `T` gives `f(k+1) <= delta - c_*^Syl (1 - f(k))`.
4. **Recursion.** Steps 1 and 3 give `|f(k+1) - delta f(k)| <= delta - c_*^Syl <= eps delta`. With `delta <= 1/2`
   this gives `|f(k) - delta^k| <= 2 eps delta`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 39.4 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Exact globality makes both corners fixed-point-free, the triangular count gives the upper recursion, and the error sum is at most `eps delta / (1 - delta) <= 2 eps delta`. Not decision-level: the kill-D route still needs `sylvester-disjoint-cylinder-defects-strictly-submultiplicative`.*
