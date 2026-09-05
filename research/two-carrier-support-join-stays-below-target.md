---
rg: 2
id: two-carrier-support-join-stays-below-target
kind: claim
title: The join of two hidden-sign carrier supports stays below the one-atom target
distinct_from:
  two-c-conjugate-g2-mixed-carriers-collapse-to-one-orientation: that treats products of the two carriers; this bounds their support join and therefore every complex linear combination, including interference terms.
---

Use the two carriers `Y_i`, hidden signs `Z_i`, and sign projections
`G_(sigma,+)` of `two-c-conjugate-g2-mixed-carriers-collapse-to-one-orientation`.
Put `X_i=G_(sigma,+)Y_iG_(sigma,+)` and `R=e_0+e_1`. Their initial
support join is

```text
L_sigma=G_(sigma,+)(1-(1-Z_0)(1-Z_1)/4).
```

For every pair of complex coefficients `lambda_0,lambda_1`,

```text
supp abs((lambda_0 X_0+lambda_1 X_1)R)
 <= supp abs(L_sigma R).
```

The existing exact cyclotomic calculation in the derivation gives
normalized ranks `41/768` for `sigma=+` and `13/256` for `sigma=-`.
Both are below the target trace `1/18`; the larger rank misses it by
`5/2304`. Any additional left contraction preserves this upper bound.
This statement concerns the specified finite carrier model and does not
exclude a different group-word construction.

## Attempts

The surviving route separates the coefficient-independent support bound
from its finite incidence calculation. Establishing the required
two-carrier identities is still a prerequisite; naming this missing target
does not replace that prerequisite with a new direct-proof assertion.

DERIVATION
two-carrier-linear-interference-rank-proof
