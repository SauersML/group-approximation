---
rg: 2
id: even-weil-two-carrier-gauss-angle-proof
kind: route
title: Evaluate the cross-exit Gauss coefficient in the Schrödinger model
target: even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two
requires:
  - two-cubic-residual-carriers-recover-the-deleted-source
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
---

First record the scalar two-carrier formula.  Let `U_1,U_2` fix a unit
vector `q`, put `Y_i=XU_i`, assume `Y_i^3=1`, and set

```text
a=<q,Xq> in (0,1),
b=<Y_1^2q,Y_2^2q>=<Xq,U_1^*U_2Xq>.                    (EWG1)
```

Both cyclic carriers contain `L=span(q,Xq)`.  If `e_i=Y_i^2q`, then the
orthogonal projection of `e_i` onto `L` has coefficients `a/(1+a)` on
`q,Xq`.  Hence, for the two exit vectors

```text
r_i=e_i-(a/(1+a))(q+Xq),
```

one has

```text
||r_i||^2=(1-a)(1+2a)/(1+a),
<r_1,r_2>=b-2a^2/(1+a).                               (EWG2)
```

The non-source principal cosine is therefore

```text
|b-2a^2/(1+a)| / ((1-a)(1+2a)/(1+a)).                 (EWG3)
```

Now use the standard Schrödinger normalization at `p=1 mod 8`.  Here
`a=p^(-1/2)`, both `U_1=S^2` and `U_2=RS` fix `q`, and `Xq` is the normalized
constant vector.  With `zeta=exp(2 pi i/p)`, take

```text
(Sf)(x)=zeta^(x^2/4)f(x),
(Rf)(x)=f(2x),                                        (EWG4)
```

where the quadratic character of two is `+1`.  Direct substitution gives

```text
b=<Xq,S^(-2)RSXq>
  =(1/p) sum_(x in F_p) zeta^(x^2/2)
  =p^(-1/2)=a.                                        (EWG5)
```

The last equality is the standard quadratic Gauss sum: both `2` and `-1`
are squares for `p=1 mod 8`, so the normalized phase is `+1`.  Substituting
`b=a` into `(EWG3)` yields

```text
cos_exit=a/(1+2a)=1/(sqrt(p)+2).                       (EWG6)
```

It is strictly below one, so the only intersection is the common source
line.  Orthogonal sums take the maximum of the non-source principal
cosines, proving the heterogeneous and multiplicity statements.

