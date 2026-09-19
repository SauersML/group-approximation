---
rg: 2
id: rank-deficient-return-has-a-singular-value-plateau
kind: claim
title: A rank-deficient return has a full singular-value plateau
distinct_from:
  rank-deficient-return-row-has-operator-norm-one: that records the largest singular value and the resulting operator-norm obstruction; this identifies at least the full rank deficit many unit singular values and therefore controls every Schatten and Ky Fan norm simultaneously.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that gives one normalized Hilbert--Schmidt lower bound for an arbitrary rectangular block; this gives the complete rank-deficit spectral statement for a return cut from a unitary or approximate isometry.
---

Let `e,f` be projections on a finite-dimensional Hilbert space, put

```text
r=rank(e),              s=rank(f),              r>s,
```

and let `J` be unitary.  For

```text
L=(1-f)Je
```

the singular value `1` has multiplicity at least `r-s`.  Equivalently,

```text
dim ker(1-L^*L) >= r-s.                               (SVP1)
```

Consequently, for every `0<p<infinity`,

```text
Tr(|L|^p) >= r-s,                                     (SVP2)
```

and every Ky Fan norm containing at least one of these directions sees the
same plateau.  In an ambient `d`-dimensional matrix algebra, the normalized
Schatten norms satisfy

```text
||L||_(p,norm) >= ((r-s)/d)^(1/p),                    (SVP3)
```

while `||L||_op=1` is the endpoint `p=infinity`.

The statement is robust for an approximate isometry.  If `T` satisfies

```text
||T^*T-1||_op <= eps < 1
```

and `L_T=(1-f)Te`, then at least `r-s` singular values of `L_T` are at least
`sqrt(1-eps)`.  Hence

```text
Tr(|L_T|^p) >= (r-s)(1-eps)^(p/2).                    (SVP4)
```

This quantitative form allows the return operator itself to be polar
corrected or otherwise perturbed without losing the dimension-free rank
obstruction.

