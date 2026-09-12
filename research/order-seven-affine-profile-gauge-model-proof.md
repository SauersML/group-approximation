---
rg: 2
id: order-seven-affine-profile-gauge-model-proof
kind: route
title: Distribute even sign sets around seven-cycle reservoir orbits
target: order-seven-moving-cuts-realize-both-affine-profiles
requires:
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
  - moving-order-seven-stage-gauges-have-coboundary-drift
---

All conjugates `U_i^kD_iU_i^(-k)` are diagonal in the coordinate basis and
therefore commute.  On one seven-cycle, every coordinate sees the negative
sign once for each negative coordinate in that cycle as `k` runs from zero
to six.  Its contribution to the product is consequently `(-1)^m`, where
`m` is the number of negative coordinates in the cycle.  The displayed
cycle counts are all even; fixed coordinates for row 2 have positive sign.
This proves `(OAP3)`.

The negative ranks are `4+4+4+2=14` and `2+2+2+2=8`, proving `(OAP2)`.
The controlled-reflection rank formula from the affine theorem gives

```text
Phi_(1/4)(1/2)=1/2,
Phi_(1/8)(5/6)=7/8-(3/4)(5/6)=1/4.                   (OAPP1)
```

Two self-adjoint involutions in a finite matrix algebra are unitarily
conjugate exactly when their negative ranks agree, so source reflections
with fractions `1/2` and `1/4` give the asserted exact selector rows.

Finally, the product of the seven maps in `(OAP4)` is

```text
M_i^7 tensor (D_(i,6)...D_(i,0))=1.                  (OAPP2)
```

Realize them as the seven off-diagonal blocks of a unitary cyclic shift on
the orthogonal sum of seven equal stage spaces.  Every transition then has
full source and range Gram and zero moving boundary.  Substitution of
`R_(i,k)=C_(i,k)` or `R_(i,k)=M_i tensor 1` proves the two assertions about
the mixed square directly.
