---
rg: 2
id: occurrence-local-dimension-game-collapse-proof
kind: route
title: Choose a dimension witness larger than the current matrix after local decoding
target: occurrence-local-dimension-games-force-mark-collapse
requires: []
---

Choose `delta>0` with `C delta^2<eta`.  Suppose `(OGC1)` holds with
`epsilon<delta`.  For every `N`, `(OGC2)` gives a strategy for `G_N` of value
greater than `1-eta`, hence

```text
C_0 d>=D_N.                                             (1)
```

The left side of `(1)` is fixed while `D_N->infinity`, a contradiction.
This proves `(OGC3)`.

If `Gamma` were hyperlinear, canonical-trace microstates would have relator
defect tending to zero.  Since `J` is nontrivial, their marked distance tends
to `sqrt(2)`.  For `beta<sqrt(2)` they eventually violate `(OGC3)`, proving
nonhyperlinearity.
