---
rg: 2
id: steinberg-first-coupled-plane-transfer-absorber-proof
kind: route
title: Construct the three-plane doubly-centered absorber
target: steinberg-coupled-plane-transfer-has-marginal-absorber
requires: []
---

Put every value at `c=0` equal to zero, and put every unlisted `b`-plane
equal to zero.  For `c!=0`, define

```text
g(a,-4,c)   =(5/c)(a+1/2+5/c),
g(a,-4/5,c)=c^(-2)-5(a+1/2)c^(-1),
g(a,0,c)    =-10c^(-2).                              (FCPA1)
```

This is nonzero because, for example,
`g(-1/2,-4/5,1)=1`.  Since

```text
sum_(x!=0) x^(-1)=sum_(x!=0) x^(-2)=0
```

for `p>=7`, every point marginal `P_g(a,b)=sum_c g(a,b,c)` vanishes.
Also `sum_a a=0` and `p=0`, so every fixed-`(b,c)` column sum vanishes;
equivalently each such column lies in `im(1-q)`.

For the plane marginal, `c=0` is zero.  If `c!=0`, the three supported
incidences `b=ac-d` occur at

```text
a=(d-4)/c,       a=(d-4/5)/c,       a=d/c.
```

The first two values in `(FCPA1)` are

```text
5(d+1)c^(-2)+5(2c)^(-1),
5(1-d)c^(-2)-5(2c)^(-1).
```

Their sum is `10c^(-2)`, which the `b=0` value cancels.  Hence
`H_g(c,d)=0`.

Finally, on `b=-4` the generic `u` map is

```text
A=(a-2)/5,             C=c/[5+c(a+1/2)],             (FCPA2)
```

with target plane `b=-4/5`.  Put

```text
z=C^(-1)=a+1/2+5/c.
```

Because `5(A+1/2)=a+1/2`, the target value is

```text
z^2-5(A+1/2)z=z(5/c)=(5/c)(a+1/2+5/c),
```

which is exactly the source value.  If the denominator in `(FCPA2)`
vanishes, then `z=0` and the displayed source value is zero; the transformed
tree coefficient is also zero because `P_g=H_g=0`.  At `c=0` both sides are
zero.  The point denominator `1-b=5` is nonzero for every `p>=7`.  Thus the
full coupled transfer, including all exceptional strata, holds.

It remains to realize this absorber by an actual zero-marginal `f`.  Before
correction, for `c!=0` put

```text
f_0(a,-4,c)   =-5a^2/c+(-5/(2c)-50/c^2)a,
f_0(a,-4/5,c) = 5a^2/c+(-2/c^2+5/(2c))a,
f_0(a,0,c)    =20a/c^2,                              (FCPA3)
```

and put `f_0=0` at `c=0` and on all other planes.  Since

```text
(1-q)a=-1/2,             (1-q)a^2=-a-1/4,
```

direct substitution in `(FCPA3)` gives exactly `(FCPA1)`.  The inverse-power
sums give `P_(f_0)=0`.  Direct substitution in the plane marginal gives,
independently of `d`,

```text
H_(f_0)(c,d)=K(c)=8/c^2+624/(5c^3)       for c!=0,
H_(f_0)(0,d)=0.                                       (FCPA4)
```

Indeed the `c^(-3)` numerator is

```text
-5(d-4)^2-50(d-4)+5(d-4/5)^2-2(d-4/5)+20d=624/5,
```

while the `c^(-2)` coefficient is `8`.  Again the inverse-power sums give
`sum_c K(c)=0`.  Add the `q`-invariant correction

```text
k(a,0,c)=-K(c)   for c!=0,             k=0 otherwise.
```

It leaves `(1-q)f_0=g` unchanged and preserves the point marginal.  For
`c!=0`, its plane marginal is

```text
sum_a k(a,ac-d,c)=-K(c),
```

so `f=f_0+k` has `P_f=H_f=0`.  It vanishes on `b=-1`.  On the `b=-4` Y row,
the `h^(-1)r` pair therefore vanishes by the established `b=-1` zero plane,
while the `u` pair is exactly the coupled identity proved above.  Thus this
`f` satisfies the full pointwise Y row on `b=-4` and still has nonzero
`g=(1-q)f` on both transferred planes.
