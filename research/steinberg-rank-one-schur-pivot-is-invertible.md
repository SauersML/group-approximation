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
