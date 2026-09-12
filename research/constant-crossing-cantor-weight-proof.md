---
rg: 2
id: constant-crossing-cantor-weight-proof
kind: route
title: Translate partial-prefix commutation into two tail equations
target: constant-crossing-collapses-active-cantor-weight
requires:
  - endpoint-native-heads-retain-coordinate-q-s3-retract
  - leavitt-diagonal-compression-is-elementary-amenable
---

Identify `D` with the locally constant `F_2`-valued functions on
`X={0,1}^N`.  For a diagonal coefficient `h` and a prefix monomial
`s_u t_v`,

```text
h(s_u t_v)=(s_u t_v)h
iff h(ux)=h(vx) for every x in X.                      (1)
```

For a diagonal coordinate projection, commutation with a root
`x_ij(a)` is the coefficient equation

```text
h_i a=a h_j.                                          (2)
```

Apply `(2)` first to the constant roots in `(CCW1)`.  The two opposite
roots on coordinates `7,8` give `h_7=h_8`; the constant crossing from
coordinate `4` to `8` gives `h_8=h_4`.  Write their common value as `h`.

For `a_1=s_1t_0`, equation `(1)` is `h(1x)=h(0x)`.  For
`b_1=s_0t_1` it is the same equality with the two sides reversed.  Thus
either choice in `(CCW2)` gives `(CCW5)`.  For `b_2=s_00t_1`, equation
`(1)` is `(CCW6)`.

Define `g(x)=h(0x)=h(1x)`.  Then `(CCW6)` reads

```text
g(0x)=g(x).                                            (3)
```

Because `g` is locally constant, choose a depth `d` on which its value is
determined by the first `d` bits.  Iterating `(3)` gives

```text
g(x)=g(0^d x)=g(0^infinity),                           (4)
```

so `g`, and hence `h`, is constant.  Since `h` is idempotent and
`F_2`-valued, it is zero or one.  This proves `(CCW4)`.

For the generation statement, set `a=a_1`, `b=b_2`, and `c=ba`.  The
Steinberg commutator relation first gives

```text
[x_84(b),x_47(a)]=x_87(c).                             (5)
```

The native Weyl word `w=nmn` exchanges coordinates `7,8`, so it transports
`A_1=x_47(a)` to `x_48(a)`.  If `x_87(c^k)` has been constructed, two more
Steinberg commutators give

```text
[x_48(a),x_87(c^k)]=x_47(ac^k),
[x_84(b),x_47(ac^k)]=x_87(bac^k)=x_87(c^(k+1)).       (6)
```

This proves `(CCW8)` by induction.  Prefix cancellation gives
`c=s_00t_0` and `c^k=s_(0^(k+1))t_0`; their distinct integer gradings prove
that the elements in `(CCW8)` are pairwise distinct.
