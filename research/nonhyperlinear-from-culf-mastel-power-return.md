---
rg: 2
id: nonhyperlinear-from-culf-mastel-power-return
kind: route
title: Use positive-density orbit capacity to close the Culf--Mastel reverse-Kleene route
target: non-hyperlinear-group
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - culf-mastel-positive-density-power-return
  - positive-density-power-dilation-forces-finite-depth
  - canonical-profile-kleene-higman
---

For a NONHALT instance, fix a depth `N>alpha_m^(-1)-1` and choose a spacing
`L` from its strict acceptance-contraction constant.  Send the canonical
microstate index to infinity in `(CPR1)` through depth `NL`.  The limiting
orbit Gram matrix is injective on `N+1` copies of the `alpha_m`-density
carrier, contradicting `(PDD6)`.  Thus canonical microstates collapse.

HALT gives the exact nonzero representation required by the reverse-Kleene
fixed point.  Apply `canonical-profile-kleene-higman` and effective Higman
embedding.
