---
rg: 2
id: sylvester-leavitt-defect-gap-descent-proof
kind: route
title: Normalize by the augmentation quotient, compress by commuting defect products, and bound globality by normal generation
target: sylvester-leavitt-defect-gap-and-geometric-descent
requires:
  - sylvester-rank-functions-descend-to-quotients-and-compressions
  - perfect-group-augmentation-quotient-ranks-are-fixed-point-free
  - sylvester-rank-functions-have-a-uniform-two-root-defect-gap
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-four-generated
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - leavitt-packet-linear-sofic-kills-kaplansky-target
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

## Why sufficient

* **Gap (artifact Theorem 4.1(1)).** `R^x` is perfect, so `rho_omega` is a non-augmentation rank function with
  some generator displaced by at least `1/4`. The uniform defect gap applied to `rho_omega` gives `c_0`. The root
  nilpotents are square-zero in characteristic two, so the Sylvester inequality bounds `rho_omega(D_A)` by `1/2`.
* **Descent (Theorem 4.1(2)).**
  - `iota_B(F_2[R^x])` commutes with the product `P` of defects on disjoint cylinders, so the commuting
    compression `tau = (rho_omega)_P o iota_B` is a Sylvester rank function with `tau(D) = f(k+1)/f(k)`.
  - The square-zero bound in `tau` gives the upper factor `1/2`.
  - The nine-leaf `Gamma_B` normally generates `R^x` (simplicity), and its compression semigroup generates
    `R^x` (the rigid-defect and packet nodes, as in `leavitt-rank-models-fixed-ideals-proof`). So quasi-globality
    gives `tau(X) >= 1/m_0`.
  - `tau` is then non-augmentation, its own gap gives `tau_omega(D) >= c_0`, and
    `tau(D) >= tau(X D) = tau(X) tau_omega(D)`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 26.3 (compression-semigroup generation and simplicity taken as established) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
