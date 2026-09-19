---
rg: 2
id: same-center-whitehead-gram-typing-refutation-proof
kind: route
title: Separate the tautological full-unitary Gram from the missing one-eighth selector occurrence
target: same-center-whitehead-gram-is-not-native-selector-gram
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - unequal-label-ranks-forbid-relational-reservoir-conjugacy
---

Because `[rho(W_m),F]=0`, compression gives a unitary on `FH`; multiplying
its self-Grams proves `(USG1)` without using any coefficient or selector
identity.  The proved label normal forms in `(USG2)` are both adjacent
two-qubit swaps, hence both have negative rank `2/8=1/4`.

The downstream affine theorem applies only after the distinct controlled
forms `(USG3)` have been decoded and their reservoir gauges compared.  No
displayed equality in the proposed route defines either controlled form or
identifies its reservoir factor with `V_m`.  A unitary relabeling cannot
change `1/4` into `1/8`, and adjoining a separated one-eighth label packet is
covered by the unequal-label-rank relational no-go.  Therefore the proposed
same-center route does not meet the occurrence requirement in the statement
of the native cross-Gram claim.

