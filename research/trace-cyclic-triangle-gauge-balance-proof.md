---
rg: 2
id: trace-cyclic-triangle-gauge-balance-proof
kind: route
title: Add the two return deficits and the chord rank balance
target: trace-cyclic-triangle-balances-independent-return-gauges
requires: []
---

Cyclicity in `(TCT2)` gives

```text
tr(H)-tr(G_0)<=epsilon_0.                               (TCTP1)
```

Cyclicity in `(TCT3)` gives

```text
tr(G_1)<=epsilon_1.                                    (TCTP2)
```

Finally `tr(BA)=tr(AB)`, so `(TCT4)` gives

```text
|tr(G_0)-tr(G_1)|<=epsilon_b.                          (TCTP3)
```

Insert `tr(G_0)` and `tr(G_1)` between `tr(H)` and zero, then use
`(TCTP1)--(TCTP3)` and the triangle inequality.  This proves `(TCT5)`.

