---
rg: 2
id: quotient-benign-rope-synchronization-proof
kind: route
title: Swap two copies of each finite quotient across the first rope letter
target: quotient-benign-rope-synchronizes-finite-quotients
requires: []
artifacts:
  - research/artifacts/quotient-benign-rope-synchronization-2026-08-25.md
---

For a finite quotient `beta:Q->B`, compose `sigma` with `beta` and map `K`
to the first coordinate of `B times B`.  Send the first rope stable letter
to the involution swapping the two coordinates.  Since `sigma` kills `L`,
the centralizing relations hold, so this defines a finite quotient

```text
lambda_beta:Gamma -> (B times B) semidirect C_2.
```

On `S`, the image lies in `B times B`, and its first coordinate is exactly
`beta tau`.  Hence `ker(lambda_beta|S) <= ker(beta tau)`.  Product
`lambda_beta` with an independent cofinal quotient of `Gamma`, and product
the result with `beta` on `Q`.  The kernel inclusion gives equality of the
two graph-edge kernels; the independent factors give cofinal separation.
