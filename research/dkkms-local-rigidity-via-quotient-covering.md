---
rg: 2
id: dkkms-local-rigidity-via-quotient-covering
kind: route
title: Local 99 percent rigidity of the DKKMS Grassmann 2-to-1 test follows from the quotient covering theorem with eta_1 = 10^(-5), zeta_1 = 1/128 and l_0 = 66
target: dkkms-grassmann-2to1-test-is-locally-99-percent-rigid
requires:
  - dkkms-quotient-covering-proves-99-percent-rigidity
artifacts:
  - experiments/dkkms-class-covering-2026-09-17/check_class_covering.py
---

The target asks for absolute constants `eta_1, zeta_1 <= 1/128` and `l_0` that
work for all `l >= l_0` and every `k` admissible for Corollary A. On every
3LIN input, every labelling `(A, sigma')` of `G_multi` with value
`>= 1 - eta_1` must agree, outside constraint mass `zeta_1`, with
`hon_kappa(lambda)` for some outer labelling `lambda` with
`val_(Phi_k)(lambda) >= 15/16` and `d_kappa(lambda) <= 1/64`.

Corollary T of `dkkms-quotient-covering-proves-99-percent-rigidity` states
this with `eta_1 = 10^(-5)`, `zeta_1 = 1/128` and `l_0 = 66`, for every advice
dimension `q >= 1`, both readings of `beta = log log k / k` and every smoothing
law. The proof of Corollary T is:

1. Theorem R^cl gives disagreement `<= 370 (eta + SD^cl)`.
2. At `eta <= 10^(-5)` and `SD^cl <= 10^(-5)` this is `<= 0.0074 <= 1/128`
   (Corollary N^cl).
3. `SD^cl(l, k) <= 10^(-5)` holds at every admissible `k` once `l >= 66`,
   because `SD^cl` decreases in `k` and `k >= k_A(l)` there.

The previous split of the target into `T1` (the regime `SD* <= 10^(-5)`) and
`T2` (the rest of the window) is no longer needed. The argument is uniform
over the window.

The artifact recomputes the threshold `l_0 = 66`. It gives
`SD^cl(66, k_A) = 9.28e-6`, and in the worst case, the base-2 reading with
`s = 1`, it checks the tail up to `l = 3000`. Step 5 of
`dkkms-quotient-covering-proves-99-percent-rigidity-proof` handles all larger
`l` analytically.
