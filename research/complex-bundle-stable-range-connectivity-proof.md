---
rg: 2
id: complex-bundle-stable-range-connectivity-proof
kind: route
title: Apply the stable connectivity of finite unitary classifying spaces
target: complex-bundles-realize-and-cancel-in-stable-range
requires: []
---

Rank-`r` complex bundles are classified by maps to `BU(r)`, while stable
rank-`r` classes are classified by the rank-`r` component of
`BU times Z`. The fibre sequence

```text
U(r) -> U(r+1) -> S^(2r+1)
```

and stabilization show that `BU(r)->BU` is `(2r+1)`-connected. Obstruction
theory therefore makes

```text
[X,BU(r)] -> [X,BU]
```

bijective whenever `dim(X)<=2r`. Surjectivity says that every stable class
of rank `r` is represented by a rank-`r` bundle; injectivity says that two
such bundles with equal stable classes are isomorphic. Since `r>=ceil(d/2)`
implies `d<=2r`, both conclusions follow.
