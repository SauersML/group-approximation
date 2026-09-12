---
rg: 2
id: binary-jacobson-residual-opposite-polar-quarter-gap-proof
kind: route
title: Split the opposite root across Q and ST and compute the two finite Hecke compressions
target: binary-jacobson-residual-opposite-polar-has-coarse-quarter-gap
requires:
  - binary-jacobson-constant-opposite-polar-is-finite-s3
  - binary-jacobson-native-v4-polar-orbit-leaves-one-residual
---

Since `Q` and `P_0=ST` are orthogonal idempotents in both orders, every
`Q`-labelled root in the displayed rank-three packet commutes with every
`P_0`-labelled root. Root additivity gives

```text
k=x_31(1)=x_31(Q)x_31(P_0)=k_Qk_P.                       (1)
```

Put `K=e_Qk_Qe_Q`. The rank-one `S_3` calculation from the first
prerequisite, applied in the coefficient corner `F_2Q`, gives

```text
(K+e_Q)(K-(1/2)e_Q)=0.                                  (2)
```

Thus the spectrum of `K` on `e_Q` is contained in `{-1,1/2}`, so

```text
K^2 >= (1/4)e_Q.                                        (3)
```

For the complementary factor abbreviate

```text
a=x_13(P_0),       z=x_23(P_0),       g=x_31(P_0),
p=(1+a)(1-z)/4=e_P.                                     (4)
```

The three roots lie in the standard `GL_3(F_2)` packet over the idempotent
`P_0`. Direct expansion in its complex group algebra gives

```text
64 p g p g p =4(1+a-z-az)=16p.                          (5)
```

Equivalently, for `M=pgp`,

```text
M^2=(1/4)p.                                              (6)
```

For completeness, `(5)` is the four-element character-idempotent
calculation for `H=<a,z>~=C_2^2`: expand each of the three copies of
`p=(1+a-z-az)/4`; the sixty-four signed terms cancel outside `H` and leave
coefficients `(4,4,-4,-4)` on `(1,a,z,az)`.

The two factors commute, and therefore

```text
A=FkF=KM,
A^*A=K^2M^2=(1/4)K^2e_P >= (1/16)F.                     (7)
```

This proves `(JRG3)`. If `f<=F`, then `B=fAf` and
`L=(1-f)Af`. Splitting the middle identity as `f+(1-f)` gives

```text
fA^*Af=B^*B+L^*L,                                       (8)
```

which proves `(JRG5)`. If `B` is singular, choose a unit vector
`xi in f` with `Bxi=0`. Equations `(7)--(8)` give

```text
||Lxi||^2=<A^*A xi,xi> >=1/16,                          (9)
```

hence `||L||_op>=1/4`. Otherwise `B` is invertible in the square corner
`fM_df`, so its polar has both support projections equal to `f`. This proves
`(JRG6)`.

Finally the signs listed in the second prerequisite are exactly `(JRG7)`,
so its `e_res` is under `e_Qe_P=F` and the dichotomy applies to the live
residual.
