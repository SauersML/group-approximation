---
rg: 2
id: bounded-coboundary-distance-collapse-proof
kind: route
title: Use the coboundary of one face as a bounded-weight codeword
target: constant-cochain-collective-codes-lose-distance
requires: []
---

Fix `i>=1` and an `(i-1)`-face `sigma` contained in at least one `i`-face.
Let `e_sigma` be its indicator cochain.  Since `d_i d_(i-1)=0`,

```text
d_(i-1)e_sigma in ker(d_i).
```

For a simplicial complex over `F_2`, its support is exactly the set of
`i`-faces containing `sigma`.  It is nonempty, and bounded degree bounds its
weight by a size-independent constant `D`.  Hence

```text
dist(ker(d_i)) <= D/|X_n(i)| -> 0.
```

For `i=0`, the equation `d_0 f=0` says that `f` has equal values across
every edge.  Connectivity therefore makes `f` constant, giving dimension
one.  These are algebraic facts independent of any expansion theorem.
