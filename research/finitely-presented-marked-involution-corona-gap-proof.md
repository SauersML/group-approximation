---
rg: 2
id: finitely-presented-marked-involution-corona-gap-proof
kind: route
title: Round the marked word and diagonalize any failure of the finite-stage gap
target: finitely-presented-marked-involution-corona-gap
requires:
  - bounded-relator-area-controls-opnorm-word-defect
---

Choose once and for all a van Kampen expression for `w^2` over the finite
presentation, and let `A` be its number of relator cells.  The bounded-area
operator-norm estimate gives

```text
||w(U)^2-I||_op <= A Def_R(U).                           (MIG2)
```

The rounded-involution estimate formalized as
`ApproxInvolutionCorner.norm_roundedInvolution_sub_le_sq_defect` gives

```text
||w_hat(U)-w(U)||_op <= ||w(U)^2-I||_op.                 (MIG3)
```

If `P_-(U)!=0`, the rounded involution is `-I` on a nonzero vector, so

```text
||w_hat(U)-I||_op=2,
||w(U)-I||_op >= 2-A Def_R(U).                           (MIG4)
```

Suppose first that every corona homomorphism kills `w` and `(MIG1)` fails.
Choose unitary tuples `U^(n)` in arbitrary matrix dimensions with

```text
Def_R(U^(n))<1/n,              P_-(U^(n))!=0.
```

Their generator sequences define a homomorphism from `Gamma` to the
sequential norm-matrix corona, because every defining relator converges to
the identity.  But `(MIG4)` says that the image of `w` has distance two
from the identity, a contradiction.  Therefore some uniform `gamma>0`
exists.

Conversely, let a corona homomorphism retain `w` and lift the finitely many
generator images to unitary sequences.  The defining relator defects tend
to zero.  The image of `w` is a nonidentity involution, hence has distance
two from the identity.  Equations `(MIG2)--(MIG3)` then force the negative
projection of the rounded coordinate word to be nonzero along infinitely
many coordinates.  This contradicts `(MIG1)` once the relator defect is
below `gamma`.  Hence the uniform gap kills `w` in every norm-matrix
corona, proving the equivalence.

