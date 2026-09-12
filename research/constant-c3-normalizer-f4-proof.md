---
rg: 2
id: constant-c3-normalizer-f4-proof
kind: route
title: Solve the 2 by 2 centralizer equations and split the C3 automorphism action
target: constant-c3-normalizer-is-f4-leavitt-semilinear
requires: []
artifacts:
  - research/artifacts/constant-c3-normalizer-f4-leavitt-2026-08-21.md
---

## Direct proof

For `X=[[a,b],[c,d]]`, the equation `Xr=rX` is equivalent to

```text
c=b,             d=a+b.
```

Thus the centralizer ring consists exactly of

```text
X(a,b)=aI+b r=[[a,b],[b,a+b]],       a,b in R.
```

The constant matrix `r` commutes with every scalar matrix `aI`, satisfies
`r^2+r+I=0`, and its polynomial is the irreducible polynomial of `F_4/F_2`.
Hence this centralizer ring is `R tensor_(F_2) F_4`, canonically the scalar
extension `L_(F_4)(1,2)`.  A matrix commuting with `r` is invertible in
`M_2(R)` exactly when it is a unit of this centralizer ring, since its inverse
then also commutes with `r`.

Conjugation maps the normalizer of `H` to `Aut(C_3)=C_2`, with kernel the
centralizer.  A constant transposition in `GL_2(F_2)=S_3` conjugates `r` to
`r^(-1)`, so the map is onto and splits.  On the quadratic coefficient field
this action is the nontrivial Frobenius automorphism, proving the semidirect
product description.
