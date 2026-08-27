---
rg: 2
id: fixed-commuting-lamp-fourier-calculation-proof
kind: route
title: Multiply the sign projections and telescope their transported products
target: fixed-commuting-lamps-have-robust-fourier-atoms
requires: []
---

Write `p_i^(epsilon_i)=(1+epsilon_i u_i)/2`.  For each `i`, the two choices
are complementary projections.  All the `p_i^(epsilon_i)` commute, so their
products are projections; two products with different signs contain a
factor `p_i^+p_i^-=0`.  Expanding

```text
product_i(p_i^++p_i^-)=1
```

proves `(FCA2)`.  Expanding each product in the group basis gives `(FCA3)`
and the triangle inequality gives `(FCA4)`.

For covariance, conjugation carries each source factor to a projection and

```text
||v p_i^(epsilon_i) v* -
  p'_(sigma(i))^(epsilon_i)||_2
 =(1/2)||v u_i v* - u'_(sigma(i))||_2.
```

The standard telescoping identity for two ordered products, together with
operator-norm contractivity of every factor, proves `(FCA5)`.  Cauchy--
Schwarz proves `(FCA6)`.  No matrix size enters any estimate.
