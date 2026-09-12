---
rg: 2
id: pair-sum-faces-control-shared-commutator-energy
kind: claim
title: Pair-sum faces quantitatively control all shared-coordinate commutators
distinct_from:
  quadratic-redundant-check-overlay-gives-uniform-face-gap: that estimates adjoint pinching energy after the marginals are already shared; this compares separately exact local face marginals with arbitrary shared candidate reflections.
  repeated-ldpc-shared-face-marginal-synchronization: that must correct the shared candidates while retaining parity and commutation; this only proves what average commutator information bare occurrence synchronization supplies.
  averaged-commutators-do-not-give-abelian-table: that shows the output of this estimate is insufficient for full-table abelian stability.
---

Use the pairwise redundant-check overlay of
`quadratic-redundant-check-overlay-gives-uniform-face-gap`.  For every
indexed augmented face `f` and `i in f`, let `A_(f,i)` be reflections which
commute within each fixed face.  Let `Q_i` be arbitrary shared candidate
reflections.  Put

```text
E_inc=(1/I) sum_f sum_(i in f) ||Q_i-A_(f,i)||_2^2,
I=sum_f |f|.                                               (PSC1)
```

There is a constant `C`, depending only on the original check width and on
the fixed ratio `M/L`, such that

```text
(1/L^2) sum_(i,j) ||Q_iQ_j-Q_jQ_i||_2^2 <= C E_inc.       (PSC2)
```

Consequently, equality-expander averaging followed by reflection rounding
really does turn small occurrence disagreement into small **average
all-logical-pairs** commutator energy.  The quadratic pair-sum overlay loses
no density at this step.

However `(PSC2)` is exactly the endpoint of this reduction.  By
`averaged-commutators-do-not-give-abelian-table`, its right-hand side tending
to zero does not make ordered products into an approximate multiplication
table on the finite abelian code-dual group.  The parity faces must still be
used inside a nonlinear correction/table-construction argument.
