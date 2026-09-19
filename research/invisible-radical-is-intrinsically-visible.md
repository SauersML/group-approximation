---
rg: 2
id: invisible-radical-is-intrinsically-visible
kind: claim
title: The invisible radical is itself residually finite and MF
distinct_from:
  corona-finite-index-radical-heredity: That is the positive finite-index formula; this is the exact sharpness statement showing the formula fails for arbitrary subgroups, and it fails already for a normal, amenable, residually finite one.
  mf-fails-with-elementary-abelian-kernel: That records the failure of MF along a split extension; this records the complementary fact that the kernel of that extension has trivial intrinsic residuals, so the obstruction is not located in the kernel.
artifacts:
  - GroupApproximation/Algebra/PermutationalWreathRadicalTame.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Algebra/PermutationalWreath.lean
---

For every nontrivial finite `K`, the subgroup `R_K <= W_K` that is invisible
to all five approximation theories is, considered on its own, locally finite,
amenable, residually finite, MF, and MAP, with

    Rad_MF(R_K) = Rad_fd(R_K) = Rad_lin(R_K)
                = Rad_Bohr(R_K) = Res_fin(R_K) = 1,

while inside `W_K` the same subgroup equals every one of those ambient
residuals.

Two readings.

**Sharpness.**  The finite-index identity
`Rad_MF(H) = H intersect Rad_MF(G)` cannot be extended to arbitrary
subgroups, and not even to normal amenable residually finite ones: here the
left side is trivial and the right side is everything.

**Diagnosis.**  The obstruction is not intrinsic pathology of `R_K`.  Finite
models for `R_K` exist in abundance; what fails is *extending* them along the
compressed Kazhdan action to models of the ambient group.  Any attack on the
family that tries to localize the difficulty inside the radical is looking in
the wrong place.
