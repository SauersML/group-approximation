---
rg: 2
id: sylvester-leavitt-kazhdan-fixed-ideals-global-proof
kind: route
title: Kernel containment after every right factor is transitive and stackable, so translates of the nine-leaf generators absorb the augmentation generators
target: sylvester-leavitt-kazhdan-fixed-ideals-are-global
requires:
  - sylvester-rank-functions-are-submodular-on-stacked-rows
  - perfect-group-augmentation-quotient-ranks-are-fixed-point-free
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-four-generated
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - leavitt-packet-linear-sofic-kills-kaplansky-target
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

## Why sufficient

Artifact Section 2. Write `M ≼ M'` when `psi([M W; M' W]) = psi(M W)` for every `W`.

1. **Containment from compressions (Lemma 2.1).** For `h` in `P_Gamma`, `X_(hSh^-1) = Y_h X_S = (h (x) I) X_S h^-1`
   gives `X_S ≼ X_S h^-1`. The rank invariance of part 3 of
   `perfect-group-augmentation-quotient-ranks-are-fixed-point-free` gives `X_S h^-1 ≼ X_S`.
2. **All translates (Lemma 2.2).** By transitivity (`sylvester-rank-functions-are-submodular-on-stacked-rows`) and
   right translation, `{h : X_S ≈ X_S h}` is a subgroup containing `P_Gamma^-1`, so it is `G`.
3. **Absorption (Theorem 2.3).** Normal generation gives `X = Y [X_S h_1; ...; X_S h_m]`. Closure under stacking
   gives `X_S ≼ X`. So for fixed-point-free `psi`, `psi(Z) = psi(X Z) <= psi([X_S Z; X Z]) = psi(X_S Z) <= psi(Z)`.
4. **Leavitt instance (Corollary 2.5).** `rho_omega` is fixed-point-free because `R^x` is perfect.
   - The nine-leaf subgroup `Gamma_0` has a compression semigroup generating `R^x`: the compressors come from
     `leavitt-unit-group-carries-nontrivial-rigid-defect` and `leavitt-packet-linear-sofic-kills-kaplansky-target`.
   - `Gamma_0` normally generates `R^x` (`binary-leavitt-unit-group-is-simple`).
   - Every `Gamma_B` is a `V`-conjugate of `Gamma_0`, so it has both properties.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 39.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS, constant `1`. The forward containment comes from an exact identity, the reverse uses the Frobenius step for `h` in `P_Gamma` only, and fixed-point-freeness enters only in the last line. Correction forward to the artifact's calibration remark: without the compression hypothesis, even the `1/m` bound fails for general `Z`.*
