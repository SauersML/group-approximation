---
rg: 2
id: schatten-one-corner-detector-proof
kind: route
title: Import the Schatten-one radical corner theorem
target: schatten-one-corner-detector
requires: []
artifacts:
  - notes/TRUE_SCHATTEN_ONE_RADICAL_CORNER.md
---

## Direct proof

The complete argument is `notes/TRUE_SCHATTEN_ONE_RADICAL_CORNER.md`, dated
2026-08-13, in four steps: exactification of the involution by the
involution-rounding lemma (`u_n^2=1`, `||u_n-phi_n(z)||_1 -> 0`); the negative
spectral projection `q_n=(1-u_n)/2`, nonzero for large `n` by the retention
hypothesis, asymptotically commuting with the model by centrality of `z`;
compression and polar correction in a unitarily invariant norm, giving
`psi_n : E -> U(q_n C^(d_n))`; and the conversion
`||A_n||_(2,r_n)^2 <= 2||A_n||_1/r_n <= 2||A_n||_1`, which needs the norm to
be unnormalized and is insensitive to how small `r_n/d_n` is.  In the corner
`psi_n(z) -> -1`, so the image in the tracial ultraproduct is hyperlinear and
retains `z`; a sofic image would kill every element of `Rad_sof(E)`.  End
proof.

## Trust surface

This is a corpus import, not a re-derivation: the route asserts the artifact
carries the complete argument.  The one non-obvious ingredient is the
involution-rounding lemma for unitarily invariant norms, which the artifact
uses by name; a formalization pass should check it first.
