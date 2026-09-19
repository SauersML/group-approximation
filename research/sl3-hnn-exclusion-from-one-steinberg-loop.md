---
rg: 2
id: sl3-hnn-exclusion-from-one-steinberg-loop
kind: route
title: Use one mixed Steinberg loop to force a scalar gap in the free HNN lamp Gram matrix
target: sl3-ambient-outliers-carry-no-free-hnn-letter
requires:
  - full-hnn-regularity-is-a-quasiregular-unitary-orbit
---

**INVALIDATED PROPOSAL.**  Insert

```text
[x_23(1),x_31(-1)]=x_21(-1)
```

into the scalar Gram identities of the stable-letter conjugacy orbit and
attempt to obtain an additional orthogonality or rank deficit.

`one-steinberg-loop-is-hnn-gram-neutral` proves that both paths merely name
the same coset endpoint and hence the same lamp atom.  Their Gram rows agree
identically.  A proof may still use this relation through matrix-coordinate
coherence across the full dyadic tower, but not as a one-loop scalar moment
inequality.
