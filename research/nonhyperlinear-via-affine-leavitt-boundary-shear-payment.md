---
rg: 2
id: nonhyperlinear-via-affine-leavitt-boundary-shear-payment
kind: route
title: Take the finite-depth root-boundary estimates through the canonical microstate double limit
target: non-hyperlinear-group
requires:
  - affine-leavitt-steinberg-mark-is-fd-invisible
  - steinberg-root-shear-plancherel-covariance
  - relative-leavitt-active-subspaces-expand-by-two
  - fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity
  - affine-leavitt-boundary-shear-payment
---

The marked word `w_A` is nonidentity by
`affine-leavitt-steinberg-mark-is-fd-invisible`.  The boundary-shear claim
supplies `(FDM1)` with `b_N=2^-N`.  Applying
`fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity` therefore
rules out a canonical-trace matrix microstate sequence for `Gamma_A` and
makes this already explicit finitely presented property-`(T)` group
nonhyperlinear.

This route deliberately does not seek a modulus uniform in depth or valid on
arbitrary trace profiles.  The only remaining estimate is the one-step
paired-root boundary payment inside `(BSP2)`.
