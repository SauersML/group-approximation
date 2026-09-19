---
rg: 2
id: universal-residual-wordization-collapse-proof
kind: route
title: Evaluate the proposed residual bound in the faithful regular trace
target: universal-residual-wordization-collapses-carrier
requires:
  - fano-cap-sequential-products-form-an-algebraic-naimark-carrier
  - algebraic-selector-mixing-frame-collapses-forbidden-sector
---

The defining words vanish in the regular representation, so `(URW1)` gives
`kappa tau(X^*X)<=0`.  Positivity and faithfulness give `X=0`.  Equation
`(URW2)` is the one-line tracial calculation

```text
sum_i tau(X^*K_i^*K_iX)=tau(X^*X).
```

Thus the exact tight-frame identity strengthens the obstruction rather than
evading it: any universal word payment for all its rows is a universal word
payment for `X` itself.
