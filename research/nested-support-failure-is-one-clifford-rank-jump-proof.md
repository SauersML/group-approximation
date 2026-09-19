---
rg: 2
id: nested-support-failure-is-one-clifford-rank-jump-proof
kind: route
title: Compute the four binary determinants of the two-idempotent pairing
target: nested-support-failure-is-one-clifford-rank-jump
requires: []
---

Substitution in `(NSR1)` gives respectively

```text
[[0,0],[0,0]],  [[1,0],[0,0]],  [[1,1],[1,1]],  [[0,1],[1,1]].
```

The first has rank zero, the middle two have rank one, and the determinant of
the last is `1` over `F_2`, so the last has rank two.  This is `(NSR2)`.
