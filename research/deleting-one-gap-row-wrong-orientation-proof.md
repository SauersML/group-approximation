---
rg: 2
id: deleting-one-gap-row-wrong-orientation-proof
kind: route
title: Subtract the retained Gram energy from the finite-game gap
target: deleting-one-gap-row-has-the-wrong-orientation
requires:
  - one-gram-vector-decodes-a-finite-bcs-strategy
---

The Gram-Rayleigh theorem gives the second inequality in `(DGR1)`.  Rearrange
the first equality:

```text
(mu_e/4)||A_(c,x)G-GB_x||_2^2
 =E_G-E_keep
 >=lambda||G||_2^2-E_keep.                             (DGR4)
```

Insert `(DGR2)` and divide by `mu_e/4`.  This is `(DGR3)`.  No compactness,
attainment of the finite game value, or choice of a minimally unsatisfiable
subgame is used.

