---
rg: 2
id: titz-witzel-cyclic-affine-ansatz-proof
kind: route
title: Evaluate the twelve reduced relators in the affine group of an odd cyclic set
target: titz-witzel-cyclic-affine-ansatz-has-linear-defect
requires:
  - titz-witzel-sofic-gate-has-only-seven-relators
---

Write an affine permutation `i |-> ui+v` as `(u,v)`, with composition

```text
(u,v)(u',v')=(uu',uv'+v).                                (1)
```

For `(TCA1)`, direct substitution in `(TWS3)`, using `2h=1`, gives

```text
A=C=(-1,a+2),               B=E=F=H=(1,0),
D=(-1,a+1),                 S=(-1,a-h).                  (2)
```

Every map `(-1,b)` is an involution, proving all seven square equations.
Equation (2) also displays directly the redundancy behind four of them:
in arbitrary permutations one has the free-word identities

```text
B=zEz^(-1),                 H=yEy^(-1),
F=x^(-1)Hx.                                                   (3)
```

The five coupling words now evaluate, in order, to

```text
A C D B       =(-1,a+1),
x z C S       =(-1,a-3),
A E D F       =( 1,1),
D F E H       =(-1,a+1),
D S F E       =( 1,h+1).                                  (4)
```

On an odd cyclic set, `i |-> -i+b` has exactly one fixed point, since `2`
is invertible modulo `n`.  A nonzero translation has no fixed point.  The
third map in (4) is translation by `1`.  For the fifth, `h+1` is nonzero
when odd `n>=5`: otherwise `n` would divide `2(h+1)=3`, forcing `n=1` or
`n=3`.  Therefore (4) has respectively

```text
n-1, n-1, n, n-1, n
```

moved points, which proves `(TCA2)`.

Finally, `y^8` is translation by `8`.  No odd `n>=5` divides `8`, so this
translation has no fixed point and `d_H(y^8,1)=1`.
