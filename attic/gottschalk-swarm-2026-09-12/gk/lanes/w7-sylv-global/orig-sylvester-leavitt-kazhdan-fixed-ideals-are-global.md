---
rg: 2
id: sylvester-leavitt-kazhdan-fixed-ideals-are-global
kind: claim
title: The augmentation quotient of every Sylvester rank function on the binary Leavitt unit group algebra is exactly global on cylinders
distinct_from:
  leavitt-rank-models-kazhdan-fixed-ideals-are-global: that is globality of fixed right ideals for rank-ultraproduct models, where fixed ideals are principal; this is the same statement for every Sylvester rank function, phrased through ranks of products, where no fixed ideal exists.
  perfect-group-augmentation-quotient-ranks-are-fixed-point-free: that proves the bound rho_omega(X_S Z) >= rho_omega(Z)/m; this asks for equality.
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, `X = (g_i - 1)^T` for generators of `R^x`, and `rho` any non-augmentation
Sylvester matrix rank function on `F_2[R^x]`. For every proper cylinder `B` and every matrix `Z`,
`rho_omega(iota_B(X) Z) = rho_omega(Z)`.

**Why it matters.** It is the class-(A) form of globality on cylinders (Lemma 3.0 of
`research/artifacts/two-root-defect-descent-gap-2026-09-12.md`). With it, the compressed rank functions of
`sylvester-leavitt-defect-gap-and-geometric-descent` are fixed-point-free, the lower descent constant becomes the
exact infimum `c_*^Syl`, and the lower-bound half of near-minimal multiplicativity goes through.

## Attempts

- 2026-09-12 `w5-regular-rankfn` (artifact Sections 3 and 5.1).
  - **Proved:** invariance `rho_omega(iota_B(X) h Z) = rho_omega(iota_B(X) Z)` for every `h` in `R^x`, by the
    Frobenius inequality on the compression semigroup, and the bound `>= rho_omega(Z)/m_0`, by normal generation.
  - **Where it stops:** the regular proof's last step, "a principal right ideal containing a conjugate of equal rank
    equals it", has class-(A) form "`psi(M_1 W) = psi(M_2 W)` for all `W` implies
    `psi([M_1; M_2] W) = psi(M_1 W)`". It holds for regular rank functions and would follow from
    `sylvester-rank-functions-on-leavitt-units-are-regular`; I found no proof from the Sylvester axioms.
