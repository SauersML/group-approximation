---
rg: 2
id: s3-weighted-budget-optimization-proof
kind: route
title: A two-by-two characteristic polynomial factors at the optimal budget
target: s3-weighted-budget-optimization
requires: []
---

By homogeneity set `q=1` and write `r=p/q`.  The smaller standard-sector
eigenvalue

```text
lambda(r)=r+1-sqrt(r^2-r+1)
```

is the smaller root of

```text
z^2-2(r+1)z+3r=0.                                     (1)
```

Assume first `A=a^2>0` and `B=b^2>0`, and put

```text
F=a^2+ab+b^2,
M=3/(2F),
z=M(ra^2+b^2).
```

A direct substitution into the left side of `(1)` gives the exact factorization

```text
z^2-2(r+1)z+3r
 = -3[a^2 r+2ab r-2ab-b^2]^2/(4F^2) <=0.             (2)
```

Thus `z` lies between the two roots of `(1)`, in particular

```text
lambda(r) <= M(rA+B)
```

for every `r>0`.  Therefore the desired ratio is at most `M`.

Equality in `(2)` occurs at

```text
r=b(2a+b)/(a(a+2b)),
```

which is positive and gives `lambda(r)=M(rA+B)`.  Hence the supremum is exactly

```text
M=3/(2(A+B+sqrt(AB))).
```

If one of `A,B` vanishes, let the displayed maximizing ratio tend to its
boundary value.  The same formula follows by continuity (equivalently from
`lambda(r,1)->3/2` as `r->infinity` and
`lambda(r,1)/r->3/2` as `r->0`).