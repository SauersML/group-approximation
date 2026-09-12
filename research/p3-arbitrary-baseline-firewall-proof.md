---
rg: 2
id: p3-arbitrary-baseline-firewall-proof
kind: route
title: Use the identity and Weyl involutions over the collapsed mod-three dilation
target: p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment
requires: []
---

Work in `PSL_2(F_3)`.  Let

```text
R = [ 2  0 ] = -I = 1 in PSL_2(F_3),
    [ 0  2 ]

T = [ 1  1 ],                W = [ 0 -1 ].             (P3P1)
    [ 0  1 ]                     [ 1  0 ]
```

Put `X=1` and `X_0=W`.  The BS relation is immediate:

```text
R T R^(-1)=T=T^4,
```

because `T^3=1`.  Both involution and inversion rows hold for `X`, while
for `X_0` they follow from `W^2=-I=1` in the projective group and `R=1`.

For `X=1`, the two cubic products are `T` and `T^2`, so `(P3A1)` holds.
For `X_0=W`, direct multiplication gives

```text
WT   = [ 0 -1 ],             WT^2 = [ 0 -1 ].          (P3P2)
       [ 1  1 ]                    [ 1 -1 ]
```

The first matrix has determinant one and trace `1`, hence its cube is
`-I`; the second has determinant one and trace `-1`, hence its cube is
`I`.  Both cubes are the identity in `PSL_2(F_3)`.  Since `R=1`, these are
exactly the two cubic rows in `(P3A1)`.

The relative gauge is `c=XX_0=W`.  But

```text
WT = [ 0 -1 ],               TW = [ 1 -1 ],            (P3P3)
     [ 1  1 ]                     [ 1  0 ]
```

and these matrices are neither equal nor negatives of one another.  Thus
`[c,T]` is nontrivial in `PSL_2(F_3)`.

Finally use the left regular representation of this finite group.  The two
group elements `cT` and `Tc` are distinct, so their regular matrices are
orthogonal in normalized Hilbert--Schmidt inner product and

```text
||cT-Tc||_2=sqrt(2).                                  (P3P4)
```

Every presentation residual above is zero.  Direct sums preserve both
zero residual and `(P3P4)`, proving the amplification-stable firewall.

