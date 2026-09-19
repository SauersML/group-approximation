---
rg: 2
id: common-schur-residual-hyperplane-proof
kind: route
title: Test nondegeneracy by one reciprocal bilinear evaluation
target: fanizza-schur-menu-has-common-codimension-one-residual
requires:
  - invertible-direction-schur-rank-compiler
---

Let `U` be invertible, and take nonzero column vectors `alpha,beta`.  Put

```text
P_0=ker(alpha^T),
Q_0=ker(beta^T).
```

A vector `q in Q_0` lies in the right radical of the restricted pairing
`p^T U q` precisely when `Uq` annihilates `P_0`, hence when

```text
Uq in span(alpha).
```

The only possible nonzero radical vector is therefore `U^-1 alpha`, and it
belongs to `Q_0` exactly when

```text
beta^T U^-1 alpha=0.                                  (CRH4)
```

Since `P_0,Q_0` have equal dimension, the restriction is nondegenerate iff
the scalar in `(CRH4)` is one.

For the field-multiplication pencil and `alpha=1`, the vectors

```text
U(x)^-1 alpha=a(x)^-1
```

are the sixteen reciprocal evaluation vectors.  The archived compiler proves
they form an `F_2` basis.  Hence there is a unique `beta` taking value one on
all of them.  Exact Gaussian elimination gives `beta=0x4ddc`.

The replay script evaluates the same scalar for every nonzero derivative
multiplier and then independently forms bases for `P_0,Q_0` and computes all
restricted ranks.  It returns rank fifteen for all sixteen value forms and
for the nine reset values in `(CRH2)--(CRH3)`.  In particular `0x2ce6`, one of
the original coordinate directions, is compatible.

Finally, `GL_4(F_2)` acts transitively on the nonzero selector directions.
Precomposing `x` by a selector basis change preserves the affine value set and
sends any prescribed gauge direction to the compatible coordinate.  The
truth-table row remains unrestricted because the reciprocal vectors are a
basis.  This proves the compiler statement.

