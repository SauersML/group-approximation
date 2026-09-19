---
rg: 2
id: nested-common-cut-pythagoras-proof
kind: route
title: Group leaf block pairs by their lowest common ancestor
target: nested-common-cuts-have-exact-pythagorean-boundary-ledger
requires: []
---

Fix `i`.  Expand `Q_i` in the final leaf blocks:

```text
Q_i=sum_(a,b) f_a Q_i f_b.
```

The blocks are pairwise orthogonal in Hilbert--Schmidt space.  For an
internal node `v`, its boundary in `(NCL1)` is exactly the sum of those
blocks `f_a Q_i f_b` for which `a` lies below one child of `v` and `b` lies
below the other.  Every ordered pair of distinct leaves has a unique lowest
common ancestor, so these collections partition all pairs `a!=b`.
Therefore

```text
sum_v b_(v,i)^2
 =sum_(a!=b)||f_a Q_i f_b||_2^2
 =||Q_i-sum_a f_aQ_if_a||_2^2.
```

Average over `i`.  Since pinching is the orthogonal projection onto the
block-diagonal subspace and `||Q_i||_2=1`, the last quantity is at most one.
This proves all asserted identities.
