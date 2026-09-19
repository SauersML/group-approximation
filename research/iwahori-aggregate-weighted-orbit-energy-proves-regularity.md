---
rg: 2
id: iwahori-aggregate-weighted-orbit-energy-proves-regularity
kind: route
title: Identify the aggregate finite-cycle inequality with Koopman spectral regularity
target: weyl-defect-koopman-spectral-regularity
requires:
  - iwahori-cubics-control-aggregate-weighted-bs-orbit-energy
---

On a dyadic band `t/2<|1-lambda|<=t`,

```text
|hat e'(lambda)|^2/|1-lambda|^2
 <=4 t^(-2)|hat e'(lambda)|^2.
```

Summing first inside each band and then over the disjoint dyadic bands turns
`(IAG1)` into `(KSR)` up to the factor four.  The fixed algebra and the
high-frequency complement are handled by the direct bounds already recorded
in `weyl-defect-koopman-spectral-regularity`.  Hence the corrected aggregate
finite-cycle inequality proves the target without the false pointwise
`t^epsilon` gain.
