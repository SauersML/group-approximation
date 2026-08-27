---
rg: 2
id: steinberg-p-five-b-zero-boundary-absorber-proof
kind: route
title: Construct the exact p=5 projective boundary absorber
target: steinberg-p-five-b-zero-boundary-absorber
requires: []
---

Put

```text
v_a(c)=f(a,0,c),             v_a(infinity)=-P(a,0),
w_a(y)=v_a(1/y)
```

on `P^1(F_5)`.  Exact substitution in `Y(a,0,c)`, including the `u`- and
`r`-tree exceptions, gives at every actual chord `y!=0`

```text
(w_a-w_(a+3))(y)-(w_a-w_(a+3))(y+a+3)
 +w_(3a)(2y)-w_(3a)(2y+1)=0.                         (P5BA2)
```

The omitted `y=0` equation follows by summing `(P5BA2)` over affine `y`:
all four affine arguments are permutations.  The `y=infinity` equation is
`0=0`.  The exceptional anchor from `(SYB1)` becomes

```text
w_1(y)=kappa  for y in F_5,       w_1(infinity)=0.
```

Taking `w_a=0` for `a!=1` satisfies `(P5BA2)` for every `a,y` and arbitrary
`kappa`.

The five `X(1,0,c)` equations also admit an exact absorber.  Set

```text
f(1,0,0)=0,              f(1,0,c)=kappa  for c!=0,
f(a,0,c)=0               for a!=1,

(f(4,2,c))_(c=0)^4=(-kappa,-kappa,-kappa,0,-kappa),
```

and set every other value used by this local subsystem to zero.  For

```text
G_0(s)=f(4,0,s)-f(2,0,s),
G_1(z)=f(4,0,z)-f(4,2,z+3),
```

this gives

```text
G_0=0,        P(4,0)=0,        P(4,2)=kappa,
G_1=(0,kappa,kappa,kappa,kappa).
```

Substitution verifies all five `X(1,0,c)` equations, including the `c=1`
tree exception.

Finally, the previously isolated residual is not an additional equation.
The `t=2` anchor row gives

```text
G_1(4)=kappa-G_0(3),
```

so that residual reduces to

```text
P(4,0)+f(2,0,1)+G_0(3)=0.                            (P5BA3)
```

But `(P5BA3)` is the negative of the omitted `y=0` instance of `(P5BA2)`
at `a=4`, namely

```text
-P(4,0)-f(4,0,3)+f(2,0,3)-f(2,0,1)=0.
```

It follows by summing the actual `Y(4,0,c)` rows.  Thus the entire stated
subsystem leaves `kappa` free.
