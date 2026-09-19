---
rg: 2
id: uniform-fano-profile-via-central-mark-or
kind: route
title: Enumerate every cap profile and apply the exact finite LCS OR
target: culf-mastel-rstar-uniform-fano-cap-profile
requires:
  - culf-mastel-rstar-fixed-language-gap-is-published
  - rstar-fano-cap-support-preserves-nonru-affine-relaxation
  - rstar-cap-support-is-one-character-row
  - finite-lcs-product-sign-is-exact-or
  - culf-mastel-rstar-halt-model-has-fano-cap-support
---

For a fixed finite `R_*` instance with `m` contexts, enumerate the `7^m`
profiles of maximal caps.  At a context, a profile adds one of the seven
nonzero parity rows `(FMC3)` to the odd four-parity row.  Every Fano cap is
contained in one of these maximal caps, so this compressed menu contains a
branch for every cap-supported model.  Apply
`finite-lcs-product-sign-is-exact-or` to the resulting finite list.

Equivalently, `rstar-cap-support-is-one-character-row` says that the HALT
model factors through one of these quotients: each branch adds exactly one
row per nonlinear context, and no enumeration of the sixty-four nonmaximal
local caps is needed.

On a halting input the required cap-supported perfect CE model satisfies one
enumerated branch, so exact LCS OR completeness gives a nontrivial output
sign.  On a nonhalting input, a marked matrix-ultraproduct output would decode
on a nonzero corner to one affine branch.  Since every cap is contained in
`R_*`, that branch would be a perfect CE solution of the original
Culf--Mastel instance, contradicting its gap.
