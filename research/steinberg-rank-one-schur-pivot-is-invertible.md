---
rg: 2
id: steinberg-rank-one-schur-pivot-is-invertible
kind: claim
title: The complete X row has an invertible interior rank-one Schur pivot
---

For every odd `p>=5`, let `M_p=pi_S X^*|_S` in the bases
`[a^i c]`, `2<=i<=p-2`, from
`steinberg-a-defect-isomorphism-on-rank-one-hasse-block`.  Prove

```text
det(M_p) != 0.                                         (SRP1)
```

Writing `r,i=2,...,p-2`, its exact entries are

```text
(M_A)_(r,i)=2^(r-i)(
  1_(r>=i) binom(p-i,r-i)
 -1_(r>=p-i)(-1)^(p-r)binom(i,r-p+i)),

M_p=M_A+diag(d_i-1),
d_2=0,                  d_i=2^(1-2i)  (i>=3).          (SRP2)
```

Equivalently, for `P(x)=sum_(i=2)^(p-2)p_i x^i`, `(SRP1)` asks that the
only solution of

```text
F(x)-F(x-1)+2P(x/4)-P(x)-(p_2/8)x^2=0,
F(x)=(1+x)P(x/(1+x)),                                 (SRP3)
```

as an `F_p`-function is `P=0`.  An exact determinant evaluation would
pivot all `S` rows and reduce the X-dual surjectivity problem to the
explicit Schur complement on `Q/S`; it does not by itself prove that
complement is invertible.

## Exact reduction

Expanding the first row of `(SRP2)` leaves only its last entry `8`, so a
cofactor reduces `M_p` to a square minor `N=W+K`.  After reversing rows,
the anti-Pascal part factors as

```text
W'_(j,v)=a_j binom(v,j)b_v,
a_j=(-1)^(j+1)2^(1-j),             b_v=2^(-v),
```

and has determinant `-1/8`.  Binomial inversion gives the exact correction
`H=W^(-1)K`, indexed by `u,v=2,...,p-3`:

```text
H_(u,2)=(u+1)/8,

H_(u,v)=2^(1-2v) binom(u+v-1,u)
 [(-1)^v-2^(u-v)+2^(u+v-1)]       (v>=3).             (SRP4)
```

Thus `det M_p=det(I+H)`.  If `Q(t)=sum_v q_vt^v`, the generating polynomial
of `Hq` is

```text
2(1-z)^p Q(-1/[4(1-z)])
 -(1-2z)^p{
    2Q(1/[8(1-2z)])-Q(1/[2(1-2z)])
    +7q_2/[32(1-2z)^2]
 }.                                                       (SRP5)
```

Consequently `(I+H)q=0` says that `(SRP5)+Q(z)` lies in
`span{1,z,z^(p-2)}`.  Homogenize

```text
Phi(X,Y)=Y^pQ(X/Y).
```

The four degree-`p` transforms use

```text
I,
g_1=(-Y/4,Y-X),
g_2=(Y/8,Y-2X),
g_3=(Y/2,Y-2X).
```

Applying the projective differential to `Phi` removes the Frobenius
kernel.  On `Sym^(p-2)` the four coefficients become exactly

```text
1,                    -1/2,          -1/2,          1, (SRP6)
```

and the result lies in the two-dimensional boundary space
`span{Y^(p-2),X^(p-3)Y}`.  Proving that this four-transform operator has no
nonzero vector with such boundary image is now an equivalent symbolic
target for `(SRP1)`.
