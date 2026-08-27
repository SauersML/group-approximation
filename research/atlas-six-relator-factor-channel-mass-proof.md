---
rg: 2
id: atlas-six-relator-factor-channel-mass-proof
kind: route
title: Evaluate both raw S3 bridges in the canonical group trace
target: atlas-six-relator-factor-retains-half-nontrivial-s3-mass
requires:
  - atlas-six-relator-leavitt-tracial-countermodel
  - atlas-charts-overlap-trivially
  - leavitt-factor-regular-charts-inner-conjugate
  - atlas-19243-forces-sign-or-standard-channel-mass
---

Use the internal chart conjugator `U` from the exact Leavitt factor model,
with `U i_1(h)U^*=i_2(h)`.  All six relators vanish there.  For either marked
nonidentity collision generator, right multiplication gives

```text
(i_1(h)U i_1(h)^*-U)U^*=i_1(h)i_2(h)^*-1.
```

Trivial chart intersection makes the group element on the right nonidentity,
so canonical group trace makes both covariance defects squared equal to `2`.
This proves `(FHM2)`.

On the sign conjugation type the two-reflection Laplacian has eigenvalue `8`;
on the standard type its eigenvalues are `2,6`; on the trivial type it is
zero.  Therefore `(FHM3)` gives the half-mass bound.  The eight-source count
from the channel-mass dichotomy gives `1/16`, while exact vanishing of the six
rows refutes `(FHM4)`.
