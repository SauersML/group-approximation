---
rg: 2
id: nonhyperlinear-from-culf-mastel-power-return
kind: route
title: Use positive-density orbit capacity to close the Culf--Mastel reverse-Kleene route
target: non-hyperlinear-group
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - culf-mastel-positive-density-power-return
  - positive-density-hs-power-overlaps-force-finite-depth
  - canonical-profile-kleene-higman
---

For a NONHALT instance, use the fixed `N_m,L_m` chosen so that `(CPR2-HS)`
is strict.  Send the canonical microstate index to infinity in the finite
overlap list `(CPR1-HS)`.  The frame-potential inequality
`positive-density-hs-power-overlaps-force-finite-depth` gives the opposite
of `(CPR2-HS)`.  Thus canonical microstates collapse.  If the stronger
operator identities `(CPR1)` are available, they imply the same overlap
bounds, so this route consumes both versions without requiring coherent
operator identification.

HALT gives the exact nonzero representation required by the reverse-Kleene
fixed point.  Apply `canonical-profile-kleene-higman` and effective Higman
embedding.
