---
rg: 2
id: p13-scalar-long-word-drift-proof
kind: route
title: Put a vanishing scalar phase on one rotation generator
target: p13-low-cluster-does-not-control-long-rotation-words
requires:
  - p13-hodge-robust-rotation-gap
---

Fix `n>=1`, write `t=pi/n`, and use the scalar tuple

```text
V1=V2=V3=1,       X=exp(i t),       Y=Z=1.
```

Every translation relation is then exact. Each affine relation has the same
rotation letter once on each side and only translation words around it, so
all nine affine defects are also zero.

## The eight rotation relators

Direct substitution gives defects

```text
|exp(3it)-1|, 0, 0, |exp(3it)-1|, 0, 0,
|exp(2it)-1|, |exp(6it)-1|.
```

Here the sixth relation `(X^(-1) Z X Y)^2=1` is exact, while the seventh
relation `(Y^(-1) Z Y X)^2=1` contributes `exp(2it)`. The elementary
chord bound

```text
|exp(i a)-1|<=|a|
```

therefore bounds every rotation-relator defect by `6t=6pi/n`.

## The P13 energy

Evaluate the six checked substitution words in repository order:

```text
YxzYX   =1,
xzYXY   =1,
Yxyxz   =exp(-2it),
XYxzY   =1,
xYxzYx  =exp(-3it),
XzYXYX  =exp(3it).
```

On the unit vector, the P13 Laplacian is consequently the scalar

```text
D_n=|exp(-2it)-1|^2+2|exp(3it)-1|^2
   <=4t^2+18t^2
   =22pi^2/n^2.
```

For all sufficiently large `n`, `6pi/n` is below the threshold in
`p13-hodge-robust-rotation-gap`. Also `D_n` tends to zero whereas its
high endpoint `lambda_+(6pi/n)` tends to the positive number `gamma`.
The proved spectral dichotomy therefore puts `D_n` in the low interval.

## The escaping word is genuine

For `r_n=(ZXY)^n`, scalar evaluation gives

```text
r_n=exp(i*n*t)=-1,
```

so its displacement is exactly two.

It remains only to check that this sequence is not padding a torsion word.
In the integral affine quotient the upper-left `3 by 3` blocks are

```text
X=[[0,1,0],[0,0,1],[1,0,0]],
Y=[[1,0,1],[0,-1,-1],[0,1,0]],
Z=[[0,1,0],[1,0,0],[-1,-1,-1]].
```

Multiplication gives

```text
A=ZXY=[[0,1,0],[0,-1,-1],[-1,0,0]]
```

and

```text
det(sI-A)=s^3+s^2-1.
```

If `A` had finite order, its three eigenvalues would be roots of unity.
Because the characteristic polynomial has odd degree, it would then have a
real root equal to `1` or `-1`; neither is a root. Thus `A` has infinite
order. More specifically

```text
e2=(0,1,0),       A e2=(1,-1,0),
A^2 e2=(-1,1,-1)
```

form an integral basis. If a positive power of `A` fixed `e2`, it would
also fix its first two `A`-translates and hence would be the identity.
Therefore the orbit `A^n e2` is pairwise distinct. The words `r_n` are
exactly the escaping conjugators taking the basis translation `e2` to
these translations.

Finally, suppose a uniform modulus bounded all rotation-word displacements
in terms of the maximum rotation-relator defect and the square root of the
P13 energy, and tended to zero at the origin. Applying it to this family
would bound the constant displacement `2` by a quantity tending to zero,
a contradiction. This proves the claim and isolates the failure of the
direct low-cluster substitution in the affine circumcenter route. QED
