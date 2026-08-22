---
rg: 2
id: perfect-lcs-via-central-tagged-one3
kind: route
title: Decompose a central-tagged ONE3 perfect-gap family into affine profiles
target: perfect-completeness-constant-soundness-lcs-compiler
requires:
  - central-tagged-one-in-three-is-a-finite-lcs-or
  - culf-mastel-one3-central-tagged-perfect-gap-family
---

Apply the central profile decomposition to the machine-indexed tagged ONE3
instance and combine its finitely many affine branches by the exact LCS OR.
HALT completeness supplies a nonzero branch sign.  A marked perfect matrix
ultraproduct on NONHALT would cut to a perfect affine branch and hence to a
perfect tagged ONE3 model, contradicting `(C13)`.  This gives the exact RE
orientation consumed by the existing reverse-Kleene solution-group route.
