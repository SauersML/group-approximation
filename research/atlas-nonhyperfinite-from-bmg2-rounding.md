---
rg: 2
id: atlas-nonhyperfinite-from-bmg2-rounding
kind: route
title: Approximate hyperfinite coefficients by bounded blocks and apply BMG2 after polar rounding
target: atlas-positive-coefficients-are-nonhyperfinite
requires:
  - leavitt-atlas-full-coefficient-purification
  - leavitt-regular-atlas-block-monomial-gap
---

Attempt: if the coefficient algebra of a positive purified certificate were
hyperfinite, approximate its finite coefficient tuple in normalized `L2` by
a finite-dimensional algebra `B`, lift `B` to the matrix stages, and polar
round the resulting approximate relative unitary inside
`M_20160(B)`.  Its coefficient algebra has bounded simple summand size, so
`(BMG2)` appears to give a positive Atlas defect, contradicting its
closeness to the certificate.

This route is invalidated by
`bmg2-does-not-exclude-hyperfinite-atlas`: the summand-size bound depends on
the requested approximation accuracy, while the gap `e_R` has no uniform
lower bound as `R` grows.  Even granting perfect finite-dimensional lifting
and dimension-free polar rounding, the argument produces only a compatible
rate inequality and no contradiction.
