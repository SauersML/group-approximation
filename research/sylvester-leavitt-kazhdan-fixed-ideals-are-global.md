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
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w7-sylv-global`, route `sylvester-leavitt-kazhdan-fixed-ideals-global-proof`;
artifact `research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md` Section 2;
verified PASS, constant 1, by `w4-vf-linear-b`, Section 39.2 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, ae0a4005ef).

Let `R = L_(F_2)(1,2)`, `X = (g_i - 1)^T` for generators of `R^x`, and `rho` any non-augmentation
Sylvester matrix rank function on `F_2[R^x]`. For every proper cylinder `B` and every matrix `Z`,
`rho_omega(iota_B(X) Z) = rho_omega(Z)`.

**General form** (artifact Theorem 2.3). Suppose the compression semigroup of `Gamma = <S>` generates `G`, and `Gamma`
normally generates `G`. Then every Sylvester rank function `psi` on `K[G]` with `psi(X Z) = psi(Z)` for all `Z` has
`psi(X_S Z) = psi(Z)` for all `Z`. The constant is `1`, and no Kazhdan property is used.

**Why it matters.** It is the class-(A) form of globality on cylinders (Lemma 3.0 of
`research/artifacts/two-root-defect-descent-gap-2026-09-12.md`). With it, the compressed rank functions of
`sylvester-leavitt-defect-gap-and-geometric-descent` are fixed-point-free, and the lower descent constant becomes the
exact infimum `c_*^Syl`. Near-minimal multiplicativity then goes through
(`sylvester-near-minimal-leavitt-defects-are-multiplicative`).

## Attempts

- 2026-09-12 `w5-regular-rankfn` (artifact Sections 3 and 5.1).
  - **Proved:** invariance `rho_omega(iota_B(X) h Z) = rho_omega(iota_B(X) Z)` for every `h` in `R^x`, by the
    Frobenius inequality on the compression semigroup, and the bound `>= rho_omega(Z)/m_0`, by normal generation.
  - **Where it stops:** the regular proof's last step, "a principal right ideal containing a conjugate of equal rank
    equals it", has class-(A) form "`psi(M_1 W) = psi(M_2 W)` for all `W` implies
    `psi([M_1; M_2] W) = psi(M_1 W)`". It holds for regular rank functions and would follow from
    `sylvester-rank-functions-on-leavitt-units-are-regular`; I found no proof from the Sylvester axioms.
- 2026-09-12 `w7-sylv-global` (artifact `sylvester-exact-globality-and-kernel-compression-2026-09-12.md`, Section 2).
  **Proved on paper.**
  - **Mechanism.** Submodularity on stacked rows (`sylvester-rank-functions-are-submodular-on-stacked-rows`) makes the
    relation `M ≼ M'`, meaning `psi([M W; M' W]) = psi(M W)` for all `W`, transitive and closed under stacking.
    - For `h` in the compression semigroup, the exact identity `X_(hSh^-1) = Y_h X_S = (h (x) I) X_S h^-1` gives
      `X_S ≼ X_S h^-1`, and the rank invariance of Proposition 3.1(2) gives the reverse.
    - The `h` with `X_S ≈ X_S h` form a group, so they are all of `G`.
    - Stacking the translates in `X = Y [X_S h_1; ...; X_S h_m]` gives `X_S ≼ X`, so `psi(X_S Z) = psi(Z)`.
  - **Where w5 stopped.** The general implication above is not proved, and it is not needed. The containment comes
    from an exact identity, and equal ranks are used only for the reverse containment.
  - **Calibration.** Over `F_2`, `A_5` on the sum-zero submodule of its 5-point permutation module is fixed-point-free,
    and `A_4` normally generates `A_5`. But `A_4` is self-normalizing, and `psi(X_S) = 3/4`. So generation by the
    compression semigroup cannot be dropped.
  - **Leads checked.** Property (T) is not used. Weakly finite corners and pullbacks through weakly finite images (U1b)
    are not needed.
