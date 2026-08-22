---
rg: 2
id: jacobi-drifted-braid-defect-proof
kind: route
title: Multiply the two drifted braid words and compute their truncated ranks
target: jacobi-drifted-braid-defect-is-extensive
requires:
  - truncated-weyl-two-chart-boundary
---

Direct multiplication gives

```text
A_u B_u A_u=[[1+u^2,u^3],[u,1+u^2]],
B_u A_u B_u=[[1+u^2,u],[u^3,1+u^2]].                       (1)
```

Their difference in characteristic two is `(JBD3)`.  The polynomial
`1+u^2` is a unit in every `R_N`, while multiplication by `u` on `R_N` has
rank `N-1` and one-dimensional kernel.  The coordinate swap `F` is
invertible, proving `(JBD4)`.

The common core from `truncated-weyl-two-chart-boundary` consists of the
vectors whose two coordinates have zero constant and top coefficients.  It
has dimension `2(N-2)`.  For example `(u,0)` lies in it when `N>=3`, while
`u(1+u^2)F(u,0)=(0,u^2+u^4)` is nonzero whenever the displayed terms are
defined; the rank calculation gives the general non-localization statement.

Since `F=F^(-1)`, multiplying the first matrix in `(1)` on the left by `F`
gives `(JBD5)`.  Its determinant is one and

```text
det(H-I)=u+u^3=u(1+u^2).                                  (2)
```

The matrix `H-I` has a unit entry `1+u^2`.  Elementary row and column
operations over the principal local ring `R_N` therefore reduce it to
`diag(1,u(1+u^2))`.  Its kernel has dimension one, which proves `(JBD6)`.

Finally any homomorphism satisfying `(JBD7)` would carry the equality of the
two words in `(JBD2)` to equality of the two matrices in `(1)`, contradicting
`(JBD3)`.  A scalar projective correction has trivial image in the
symplectic group and cannot alter this calculation.

