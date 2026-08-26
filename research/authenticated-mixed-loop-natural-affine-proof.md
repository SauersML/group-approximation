---
rg: 2
id: authenticated-mixed-loop-natural-affine-proof
kind: route
title: Compute the two affine Fox rows on the natural SL3 module
target: authenticated-mixed-loop-kills-natural-affine-gauges
requires:
  - two-torus-closures-detect-denominator-multiplicity
---

Write elements of `M rtimes F` as `(v,g)`, with

```text
(v,g)(w,l)=(v+gw,gl),          (v,g)^(-1)=(-g^(-1)v,g^(-1)). (ANP1)
```

Use the coefficient abbreviations

```text
b=x_21(-1),       t=x_32(-1),       c=x_13(1),
a_12=x_12(2),     a_23=x_23(2),
d_12=diag(2,1/2,1).                                  (ANP2)
```

All fractions below lie in `k`; odd characteristic is used only to make `2`
invertible.

## The torus row

The only translation in each rank-one torus word occurs in
`H b H^(-1)` or `H t H^(-1)`.  Since

```text
h b h^(-1)=x_21(-1/2),       h t h^(-1)=x_32(-1/2),  (ANP3)
```

the translation part of `D_12D_23` is

```text
[a_12(I-hbh^(-1))+d_12 a_23(I-hth^(-1))]lambda.       (ANP4)
```

Using elementary matrix multiplication,

```text
a_12(I-hbh^(-1))=E_11+(1/2)E_21,
d_12 a_23(I-hth^(-1))=(1/2)E_22+(1/2)E_32.            (ANP5)
```

The coefficient part of `D_12D_23` is `h`.  Therefore `R_tor=1`, or
equivalently `D_12D_23=H`, says that for
`lambda=(u,v,w)^T`,

```text
v=u,                    w=(1/2)u.                     (ANP6)
```

## The mixed row

Set

```text
q=h b h^(-1)=x_21(-1/2).
```

The translation part of `H b H^(-1)` is `(I-q)lambda`.
For an affine element `(z,q)` and a coefficient-only element `(0,c)`, direct
use of `(ANP1)` gives

```text
translation([(z,q),(0,c)])=(I-qcq^(-1))z.             (ANP7)
```

Consequently the two translation parts in `(AMG3)` are

```text
(I-qcq^(-1))(I-q)lambda,
h^(-1)(x_23(-1)-I)lambda,                              (ANP8)
```

respectively.  The coefficient parts agree by the Steinberg identity

```text
[x_21(-1/2),x_13(1)]=x_23(-1/2)
                   =h^(-1)x_23(-1)h.                  (ANP9)
```

Now insert `(ANP6)`.  Since

```text
(I-q)lambda=(1/2)u e_2
```

and `qcq^(-1)` fixes `e_2`, the first vector in `(ANP8)` is zero.  The
second is

```text
-(1/2)u e_2.                                          (ANP10)
```

Thus `(AMG3)` forces `u=0`.  Equation `(ANP6)` then gives `v=w=0`, proving
`lambda=0`.  Every step is componentwise on direct sums of `M`, so the same
calculation proves the multiplicity statement.

The Weyl conjugacy and the two closed returns do not enter the last two
linear equations because they already hold identically in the honest
coefficient copy of `F`.  Their role is authentication: they are precisely
what prevents replacing that coefficient copy by the scalar `C_2` sheet
packet used in `one-mixed-denominator-a2-loop-is-dyadic-tower-neutral`.

For comparison with the unrestricted sheet problem, let the four root gauges
be `P,R,Q,T`, let the denominator gauge be `G`, and put
`U=PQP`, `V=RTR`, `C=[P,R]`.  Factoring the honest congruence coordinate out
of the same two words gives `(AMG9)--(AMG10)` directly: the left side of the
mixed commutator has gauge `[GQG^*,C]`, its right side has gauge `G^*R^*G`,
and the two torus factors have gauges

```text
P^2GQG^*P^2U^*,              R^2GTG^*R^2V^*.          (ANP11)
```

This verifies that the calculation has not silently scalarized the general
enemy.  The defining natural module is one exact linear face of that system;
the arbitrary noncommutative system remains open.
