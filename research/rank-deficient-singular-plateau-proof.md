---
rg: 2
id: rank-deficient-singular-plateau-proof
kind: route
title: Apply rank-nullity and the min-max principle on the leakage kernel
target: rank-deficient-return-has-a-singular-value-plateau
requires:
  - rank-deficient-return-row-has-operator-norm-one
---

The map `fJ:eH->fH` has kernel `K` of dimension at least `r-s`.  For every
`xi in K`,

```text
L^*L xi=eJ^*(1-f)Je xi=xi,
```

because `fJxi=0`, `J^*J=1`, and `e xi=xi`.  This proves `(SVP1)`, and
functional calculus gives `(SVP2)` and `(SVP3)`.

For an approximate isometry `T`, use instead `K=ker(fT|_(eH))`.  It has the
same dimension lower bound, and for `xi in K`,

```text
||L_T xi||^2=||T xi||^2
             >=(1-eps)||xi||^2.
```

The min-max principle therefore places at least `r-s` eigenvalues of
`L_T^*L_T` in `[1-eps,infinity)`.  Raising their square roots to the `p`th
power and summing gives `(SVP4)`.

