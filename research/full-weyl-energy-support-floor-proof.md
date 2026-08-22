---
rg: 2
id: full-weyl-energy-support-floor-proof
kind: route
title: Fourier-decompose one additive family and average block overlaps
target: full-weyl-energy-support-floor
requires: []
---

Write the character decomposition of `X` as

```text
X(a)=sum_(x in H) (-1)^(a.x) P_x,
```

where the `P_x` are pairwise orthogonal projections summing to one.  Put
`p_x=rank(P_x)/d`.  For fixed `b`, orthogonality of the matrix blocks and
Fourier orthogonality in `a` give the exact identity

```text
E_a ||X(a)Z(b)-(-1)^(a.b)Z(b)X(a)||_2^2
 =4(1-sum_x ||P_(x+b) Z(b) P_x||_2^2).                  (1)
```

Indeed the `(y,x)` block has coefficient
`(-1)^(a.y)-(-1)^(a.(x+b))`; its averaged squared modulus is zero when
`y=x+b` and four otherwise.

Every block satisfies

```text
||P_(x+b) Z(b) P_x||_2^2 <= min(p_x,p_(x+b))
                           <= sqrt(p_x p_(x+b)).          (2)
```

Averaging `(2)` over uniform `b` yields

```text
E_b sum_x sqrt(p_x p_(x+b))
 =2^(-r) (sum_x sqrt(p_x))^2
 <=2^(-r) |supp(p)| sum_x p_x
 <=d/2^r.                                                (3)
```

Substituting `(3)` into `(1)` proves `(FWE1)`.

