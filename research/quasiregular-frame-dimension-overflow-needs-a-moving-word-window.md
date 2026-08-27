---
rg: 2
id: quasiregular-frame-dimension-overflow-needs-a-moving-word-window
kind: claim
title: Dimension overflow of the HNN coset frame requires a moving canonical word window
distinct_from:
  full-hnn-regularity-is-a-quasiregular-unitary-orbit: that identifies the exact ultraproduct frame; this audits the tempting finite-dimensional contradiction from the size of that frame.
  finite-swap-conjugate-moments-do-not-fold-arithmetic-double: that realizes each fixed lamp moment table in an exact finite model after discarding the arithmetic actor extension; this explains why even direct dimension counting cannot promote fixed tables to a contradiction.
---

At a matrix coordinate of dimension `d`, at most `d^2` nonzero matrices can
be pairwise Hilbert--Schmidt orthogonal.  Therefore `(HQR2)` suggests choosing
more than `d^2` cosets and contradicting finite dimensionality.  This does
not follow from the definition of a canonical microstate sequence.

For every **fixed** finite family `F subset A/C`, full regularity gives the
Gram convergence

```text
max_(x,y in F)
 |tr(k_(n,x)^*k_(n,y))-1_(x=y)| ->0.                  (QFD1)
```

But dimension overflow needs a family `F_n` with `|F_n|>d_n^2`.  The words
testing `(QFD1)` then depend on `n`.  Canonical character convergence is
pointwise on each fixed group word and supplies no control on that moving
window.  Presentation defect only compares two evaluations of a word after
one already has a bounded-area derivation; it does not force trace zero for
a nonidentity word whose length or area grows with `n`.

Hence neither exponential growth of `A/C` nor the exact quasiregular Gram
formula yields a dimension contradiction.  A valid overflow proof needs a
new quantitative injectivity-radius statement, for example a lower bound
on the canonical trace window reaching radius `c log d_n` (with errors
small enough for a rank bound), derived from the arithmetic relations
rather than assumed by reindexing.  No such rate is part of hyperlinearity,
and direct-sum replication can make the controlled word radius grow
arbitrarily slowly relative to `log d_n`: replication preserves every
normalized defect and every normalized trace already controlled at that
coordinate while multiplying `d_n` by an arbitrary factor.

Thus the extra full-HNN moments sharply identify the matrix-specific gate
but do not close it: exclude a quasiregular **unitary** frame in a matrix
ultraproduct by a dimension-free arithmetic relation, not by counting a
moving family of regular words.
