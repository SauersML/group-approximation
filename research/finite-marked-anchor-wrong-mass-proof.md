---
rg: 2
id: finite-marked-anchor-wrong-mass-proof
kind: route
title: Decompose the marked regular trace and optimize the bad character mass
target: finite-marked-involution-anchor-has-one-third-wrong-mass
requires: []
---

The `q`-corner of the left regular representation contains each marked
irreducible `pi` with multiplicity `dim(pi)`.  Its total dimension is
`|F|/2`, giving the weights `(FMA1)`.  Since `a` and `Ja` are both distinct
from the identity, the coefficient trace of `qa=(a-Ja)/2` is zero.  After
normalizing the corner trace this is exactly `(FMA2)`.

Let `g` be the total weight of types with `nu_pi=1/2`.  All remaining
characters satisfy only the universal lower bound `nu_pi>=-1`.  Hence

```text
0=sum_pi w_pi nu_pi >=g/2-(1-g),
```

so `g<=2/3`.  If `|nu_pi-1/2|<=epsilon` on the good set, replace `1/2` by
`1/2-epsilon` to get

```text
0>=g(1/2-epsilon)-(1-g),
g<=1/(3/2-epsilon),
```

which is `(FMA4)`.

Finally, on a controlled marked spin block `t=C tensor V`, normalized trace
is `tr(C)tr(V)=mu/2`.  Unitary conjugacy with `a` preserves trace, proving
`(FMA5)` and the anchor consequence.
