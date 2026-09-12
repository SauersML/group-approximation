---
rg: 2
id: koopman-carleson-suppression-proves-regularity
kind: route
title: Sum the dyadic low-mode Carleson estimate
target: weyl-defect-koopman-spectral-regularity
requires:
  - iwahori-cubics-suppress-low-bs-orbit-modes
---

On the band in `(ICL1)`, `|1-lambda|^(-2)<=4t^(-2)`.  Therefore `(ICL2)`
gives

```text
sum_(lambda in band t)
 |hat e'(lambda)|^2/|1-lambda|^2
 <=4C delta^2 t^epsilon_0.                             (KCS1)
```

Sum `(KCS1)` over `t=2^(-k)`.  Since `epsilon_0>0`, the geometric series
converges with a universal constant.  The fixed algebra was removed before
`(ICL1)` and is already bounded directly as recorded in the target claim.
The remaining high-frequency band has denominator bounded below and costs
at most a constant times `||e'||_2^2<=delta^2`.  This proves `(KSR)`.

