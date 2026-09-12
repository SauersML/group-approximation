---
rg: 2
id: full-dyadic-terminal-seam-proof
kind: route
title: Iterate the orthogonal rank decomposition down the binary tree
target: full-dyadic-split-tree-has-an-extensive-terminal-seam
requires: []
---

Iterating `(FDS1)` gives `(FDS2)` by induction on the depth.  At every step
the two children lie under their parent, so projections descending from
different nodes are orthogonal.

Equal child ranks and positivity of `E_v` imply

```text
2 rank(P_(vi))<=rank(P_v).
```

Following a path of length `R` and iterating this inequality proves
`(FDS3)`.  If `2^R>k`, every leaf rank is strictly below one and hence zero.
Taking normalized traces in `(FDS2)` proves `(FDS4)`.  Finally the three
terms in `(FDS1)` are orthogonal projections, so the node coverage residual
is exactly `E_v`; Pythagoras proves `(FDS5)`.

