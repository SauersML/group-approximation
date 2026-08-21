---
rg: 2
id: morita-rectangular-mixed-loop-proof
kind: route
title: Evaluate every root triangle as a rectangular block transvection
target: mixed-steinberg-loops-admit-morita-rectangular-model
requires: []
---

For vector spaces `(V_i)`, a rectangular coefficient `a:V_j->V_i` defines
an endomorphism supported in block `(i,j)`.  If `i,j,k` are distinct, direct
multiplication of `1+aE_ij` and `1+bE_jk` gives

```text
[1+aE_ij,1+bE_jk]=1+(ab)E_ik.
```

Nonincident blocks commute.  These calculations prove `(MSM3)` without any
equality among the dimensions of the `V_i`.  All longer mixed Steinberg
loops are pastings of these identities, and their equality is just
associativity of composition.

Choose `V=E` on a source occurrence and `V=F=E direct_sum E` on its refined
occurrence.  The coordinate inclusions and projections satisfy `(MSM2)`, so
the four nested outer-root paths evaluate to the required identity/zero
table.  Since the base field and all vector spaces are finite, the generated
block group is finite; its left regular representation supplies the asserted
unitary and trace model.
