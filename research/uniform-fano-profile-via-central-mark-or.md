---
rg: 2
id: uniform-fano-profile-via-central-mark-or
kind: route
title: Enumerate every cap profile and apply the exact finite LCS OR
target: culf-mastel-rstar-uniform-fano-cap-profile
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - rstar-fano-cap-support-preserves-nonru-affine-relaxation
  - finite-lcs-product-sign-is-exact-or
  - culf-mastel-rstar-halt-model-has-fano-cap-support
---

For a fixed finite `R_*` instance, enumerate the finite set of all contextwise
Fano-cap profiles.  For each profile form the affine LCS cutting out those
caps, then apply `finite-lcs-product-sign-is-exact-or` to this finite list.

On a halting input the required cap-supported perfect CE model satisfies one
enumerated branch, so exact LCS OR completeness gives a nontrivial output
sign.  On a nonhalting input, a marked matrix-ultraproduct output would decode
on a nonzero corner to one affine branch.  Since every cap is contained in
`R_*`, that branch would be a perfect CE solution of the original
Culf--Mastel instance, contradicting its gap.
