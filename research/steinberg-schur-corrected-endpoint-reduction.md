---
rg: 2
id: steinberg-schur-corrected-endpoint-reduction
kind: claim
title: The corrected Steinberg Schur pivot reduces to one Pascal endpoint derivative
distinct_from:
  steinberg-schur-four-transform-reduction-fails-p-seven-check: that refutes the old SRP4 cofactor; this derives a new four-transform identity and endpoint reduction directly from the corrected SRP7 matrix.
  steinberg-rank-one-schur-pivot-is-invertible: that asks for uniform invertibility; this proves an exact equivalent scalar endpoint lemma but does not prove it.
---

**ESTABLISHED CORRECTED REDUCTION.**  Let `A` be the corrected matrix
`(SRP7)`, indexed by `I={2,...,p-3}`.  For

```text
Q(t)=sum_(v in I) q_v t^v,          Phi(X,Y)=Y^p Q(X/Y),
```

define

```text
T(x)=Phi(1,1-x)-Phi(1+x,1)
     +(1/2)Phi(1,-4x)-Phi(1,-x).                    (SCE1)
```

The coefficient of `x^j`, `2<=j<=p-3`, is exactly `(Aq)_j`.  The constant
and linear coefficients vanish automatically, `deg(T)<=p-2`, and

```text
[x^(p-2)]T=-q_2/8.                                   (SCE2)
```

Consequently `Aq=0` is equivalent to the corrected homogeneous identity

```text
Phi(Y,Y-X)-Phi(X+Y,Y)
 +(1/2)Phi(Y,-4X)-Phi(Y,-X)
 =-(q_2/8)X^(p-2)Y^2.                               (SCE3)
```

This is a valid four-transform statement derived from `(SRP7)`; it does not
reuse the false `(SRP4)--(SRP6)` reduction.

There is also an exact Pascal endpoint form.  Write

```text
A=F+E-U,
F_(j,v)=binom(j+v-1,j),
U_(j,v)=1_(v>=j) binom(v,j),
E_(j,v)=1_(j+v=p)(-1)^j(2^(2j-1)-1).                 (SCE4)
```

The unit upper-triangular Pascal inverse is

```text
(U^-1)_(j,v)=1_(v>=j)(-1)^(v-j)binom(v,j).            (SCE5)
```

Put `L_(j,v)=binom(j-1,v-1)` and `c_v=(-1)^(v-1)v`.
Finite-difference summation gives

```text
F U^-1=L-1 c^T,

(E U^-1)_(j,v)
 =1_(v>=p-j)(-1)^(v-1)(2^(2j-1)-1)binom(v,p-j).      (SCE6)
```

Hence, for `R=L-I+EU^-1`,

```text
A U^-1=R-1 c^T.                                      (SCE7)
```

Row `j=2` of `R` is identically zero.  The matrix determinant lemma in this
singular rank-one form therefore gives the exact equivalence

```text
A invertible  iff  ker(R) intersect ker(c^T)={0}.     (SCE8)
```

Explicitly, the sole remaining scalar statement is: if, for
`3<=j<=p-3`,

```text
sum_(v=2)^(j-1) binom(j-1,v-1)q_v
 +(2^(2j-1)-1) sum_(v=p-j)^(p-3)
      (-1)^(v-1)binom(v,p-j)q_v=0,                   (SCE9)
```

and

```text
sum_(v=2)^(p-3)(-1)^(v-1)v q_v=Q'(-1)=0,             (SCE10)
```

then `q=0`.

For the original variable `z`, put
`Z(t)=sum z_vt^v` and `q=Uz`.  Then

```text
Q(t)=Z(1+t)-Z(1)-Z'(1)t,             Q'(-1)=-Z'(1).  (SCE11)
```

Thus the unresolved scalar is literally one endpoint derivative.

The dense Pascal baseline is completely controlled.  If `E` is deleted,
`A_0=F-U` satisfies

```text
det(A_0)=-1/2                                           (SCE12)
```

for every odd prime `p>=5`.  Indeed
`A_0U^-1=N-1c^T`, with `N=L-I` strictly lower triangular and one full Jordan
chain whose subdiagonal is `2,3,...,p-4`.  Rank-one determinant expansion
gives `-3(p-4)!`, and Wilson's theorem gives `(p-4)!=1/6`.  All remaining
difficulty is therefore carried by the special cyclotomic antidiagonal
update `E`.
