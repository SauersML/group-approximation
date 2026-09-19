---
rg: 2
id: free-root-first-detection-eigenvectors-localize-exactly
kind: claim
title: A first-detection plane eigenvector occupies exactly one top-boundary reservoir layer
artifacts:
  - GroupApproximation/PropertyT/FreeRootCharacterValuationBase.lean
distinct_from:
  free-root-top-boundary-reservoir-is-summable: that bounds the sum of all top-boundary masses; this identifies the entire norm of one joint eigenvector with the boundary layer named by its first-detection degree.
  alternating-free-ring-shears-have-strict-degree-drift: that computes the leading degrees of the candidate transporter; this is the Fourier theorem which converts a proved coefficient-character valuation into reservoir mass.
  one-sided-paired-frame-reverse-reservoir-collapse: that still must prove the paired 011 intertwiner has the required coefficient-character valuation and that its baseline packet copy persists.
---

Let `tau` be a joint sign character of a finite degree-`n` free-root plane in
an orthogonal representation, and let `z` be a joint `tau`-eigenvector.  If
the first coefficient character of `tau` is detected for the first time in
degree `n`, then

```text
planeFirstTopBoundaryMass(rho,z,n) = ||z||^2.           (FDE1)
```

The symmetric statement holds for the second coefficient and its top-boundary
mass.

This statement is exact, dimension-free, and has no leakage term.  Therefore,
once an exactified paired-frame `011` intertwiner is shown to be trivial on
all coefficient words of degree below `n` and negative on one word of degree
`n`, its full Hilbert--Schmidt mass is charged to the `n`th summable reservoir
layer.  No separate projection-rounding or overlap estimate is needed at this
step.
