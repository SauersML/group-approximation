---
rg: 2
id: tight-defect-fusion-frame-normal-form-proof
kind: route
title: Diagonalize the cubic on the ranges of the negative incidence projections
target: tight-defect-cubic-is-weighted-fusion-frame
requires:
  - shared-involution-right-ideal-interpolation-criterion
---

Because `e_i` commutes with `q_i`, the coefficient `r_i=e_iq_i` in
`(TFF1)` is a projection.  From `(TFF2)`,

```text
D_wD_w^*=4S.                                           (TFFP1)
```

The `i`th column of `(TFF4)` therefore says

```text
S r_i=(lambda/4)r_i.                                   (TFFP2)
```

The linear span of the ranges of the `r_i` is dense in `pH`.  Since `S` is
self-adjoint, `(TFFP2)` for every `i` is equivalent to

```text
S=(lambda/4)p,
```

and the converse follows by reversing the calculation.  This proves
`(TFF5)`.

For the last assertion, write

```text
wP+vQ=mu(P join Q),                 w,v>0.              (TFFP3)
```

Multiplication on the right by `P` gives `QP=cP` for one scalar `c`.
Since `Q` is a projection, `c^2=c`; hence `c` is zero or one.  The first
case gives `QP=0`.  The second gives `P<=Q`.  Applying the same argument
with `P,Q` reversed shows that the two projections are orthogonal, equal,
or properly nested.  Proper nesting is impossible in `(TFFP3)`: on
`Q-P` the eigenvalue is `v`, while on `P` it is `v+w`.  Therefore only the
orthogonal and equal cases remain.
