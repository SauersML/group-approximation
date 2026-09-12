---
rg: 2
id: stw87-approx-diagonal-bimodule-threshold-proof
kind: route
title: Read every output coordinate through its singleton corner and invoke the exact packet gaps
target: stw87-approximate-diagonal-bimodularity-order-zero-threshold
requires:
  - stw87-diagonal-expectation-order-zero-obstruction
  - stw87-diagonal-order-zero-maps-annihilate-matrix-colours
---

Fix `a in A` with `norm(a)<=1` and `x in X`.  Since

```text
p_x a p_x=a_(xx)p_x,
```

the definitions and linearity give

```text
abs(R(a)(x)-a_(xx))
 <= norm(p_x R(a) p_x-R(p_x a p_x))
    + abs(a_(xx)) abs(R(p_x)(x)-1)
 <= delta_c(R)+delta_D(R).
```

Taking the supremum over `x` and then over the unit ball of `A` proves
`(A)`.

Let `phi:C^2->A` be the two-point *-homomorphism from
`stw87-diagonal-expectation-order-zero-obstruction`.  If `R phi` is order
zero, it is one of the diagonal c.p.c. order-zero competitors in that claim.
Hence

```text
1/2
 <= max_(i=1,2) norm(R phi(e_i)-E_X phi(e_i))
 <= norm(R-E_X)
 <= delta_D(R)+delta_c(R),
```

which proves `(B)`.

Similarly, if `R iota:M_n->D` is order zero, then
`stw87-diagonal-order-zero-maps-annihilate-matrix-colours` gives

```text
1 <= norm(R iota-E_X iota)
  <= norm(R-E_X)
  <= delta_D(R)+delta_c(R).
```

This is `(C)`.
