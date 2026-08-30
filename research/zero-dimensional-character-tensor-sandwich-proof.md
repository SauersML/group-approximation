---
rg: 2
id: zero-dimensional-character-tensor-sandwich-proof
kind: route
title: Match the zero-color tensor bound with the character quotient
target: zero-dimensional-character-factor-preserves-nuclear-dimension
requires: []
---

If `dim_nuc(B)=d<infinity`, the nuclear-dimension tensor-product inequality
gives

```text
dim_nuc(A tensor_min B)
 <=(dim_nuc(A)+1)(dim_nuc(B)+1)-1
 =d.                                                   (1)
```

The spatial tensor product of the character with the identity is a
surjective *-homomorphism

```text
chi tensor id_B : A tensor_min B -> B.
```

Indeed, the nonzero range of `chi` is all of `C`, so elementary tensors map
onto a dense, hence closed, copy of `B`.  Quotient monotonicity gives

```text
dim_nuc(B)<=dim_nuc(A tensor_min B).                   (2)
```

Equations (1)--(2) prove equality when `d` is finite.  If
`dim_nuc(B)=infinity`, (2) forces the tensor product to have infinite nuclear
dimension as well.
