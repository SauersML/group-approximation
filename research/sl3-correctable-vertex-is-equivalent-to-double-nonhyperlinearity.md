---
rg: 2
id: sl3-correctable-vertex-is-equivalent-to-double-nonhyperlinearity
kind: claim
title: The canonical SL3 correctable-vertex property is equivalent to non-hyperlinearity of the fixed double
distinct_from:
  sl3-canonical-double-has-a-correctable-vertex: that is the property on microstate sequences; this identifies its exact logical strength.
  sl3-regular-arithmetic-double-fold-mark-collapse: that is a fold-word certificate with the same existence-level strength; this equivalence uses the stronger fact that every extant canonical sequence has two uniformly uncorrectable vertices.
  sl3-arithmetic-double-hyperlinear-iff-relative-embeddable: that identifies hyperlinearity of the double with an operator-algebraic relative embedding; this identifies it with a matrix-coordinate correction property.
---

For

```text
D=SL_3(Z[1/2]) *_(SL_3(Z)) SL_3(Z[1/2]),
```

the following are equivalent:

1. `D` is non-hyperlinear;
2. every canonical-character normalized-HS microstate sequence of `D` has
   at least one vertex restriction converging to exact finite-dimensional
   representations of `SL_3(Z[1/2])`, with the vertex allowed to vary with
   the matrix dimension.

Condition 2 is exactly
`sl3-canonical-double-has-a-correctable-vertex`.

If `D` is non-hyperlinear, the standard hyperlinear-microstate dictionary
says that no canonical-character microstate sequence exists, so condition 2
holds vacuously.  Conversely, if `D` were hyperlinear, such a canonical
sequence would exist.  But
`canonical-sl3-double-microstates-are-uniform-two-vertex-outliers` says that
both vertex restrictions in every such sequence stay a fixed distance from
all exact representations, contradicting condition 2.

Therefore proving the correctable-vertex property would already prove the
full fixed-candidate theorem.  It cannot serve as a logically weaker
stability lemma to be established while retaining a hypothetical canonical
microstate.
