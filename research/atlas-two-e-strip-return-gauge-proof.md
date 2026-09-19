---
rg: 2
id: atlas-two-e-strip-return-gauge-proof
kind: route
title: Collect the two E-prefixes and retain the nested monomial nuisance
target: atlas-two-e-strip-return-retains-common-gauge
requires:
  - atlas-steinberg-spare-index-independence
  - atlas-reverse-dictionary
  - atlas-first-common-rhs-return-star-has-rank-two
  - atlas-mixed-minor-needs-nuisance-quotient-rank
---

Use the `j=4` return `R=[x_14(e),x_42(e)]`. The orthogonality and St3 rows
in `(TER3)` give

```text
[x_31(E),R]=x_32(e),
[x_13(E),x_32(e)]=x_12(1).
```

The reverse dictionary identifies the last root with `p1_23`. The attached
MSI audit verifies the fully expanded word exactly.

For the quotient-rank calculation, the new row contains the reduced nested
monomial `N`, not a scalar multiple of `R`. Retaining both as nuisances gives
the matrix `(TER5)`, with increment two. Assignment `(TER6)` realizes its
kernel at every finite amplification.
