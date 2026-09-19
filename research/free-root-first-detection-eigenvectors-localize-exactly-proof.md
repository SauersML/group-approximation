---
rg: 2
id: free-root-first-detection-eigenvectors-localize-exactly-proof
kind: route
title: Collapse the simultaneous Fourier sum to the unique eigencharacter
target: free-root-first-detection-eigenvectors-localize-exactly
requires: []
artifacts:
  - GroupApproximation/PropertyT/FreeRootCharacterValuationBase.lean
---

The machine-checked theorem `iteratedPart_of_eigenvector` says that the
simultaneous sign projection of `z` is `z` at `tau` and zero at every other
sign.  The valuation hypothesis puts `tau` in
`planeFirstTopBoundarySignSet` (or its second-coordinate analogue).
Consequently the defining finite sum for the boundary mass has exactly one
nonzero term, equal to `||z||^2`.

This argument is formalized as

```text
planeFirstTopBoundaryMass_eq_norm_sq_of_eigenvector,
planeSecondTopBoundaryMass_eq_norm_sq_of_eigenvector.
```

Both statements elaborate against the Lean kernel using the warm MSI build.
