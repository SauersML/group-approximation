---
rg: 2
id: projectionless-projection-return-obstruction-proof
kind: route
title: Spectral return forces every finite-dimensional model block to be scalar
target: projectionless-ranges-obstruct-projection-return
requires: []
---

## Proof

Choose `x in C` with positive distance

```text
d=dist(x,C1_B)>0
```

from the scalars, and set `F={x}` and `epsilon=d/2`.

Suppose `D` satisfies projection return and put `p_j=e^(j)_(11)`.  Choose
`c_j in C_+` with `||c_j-p_j||<1/16`.  As in
`projection-return-central-splitting-proof`, the spectrum of `c_j` is
contained in the disjoint `1/16`-neighbourhoods of `0` and `1`, and

```text
q_j=1_((1/2),infinity)(c_j) in C
```

is a projection satisfying `||q_j-p_j||<1/8`.  It is nonzero, so
projectionlessness of `C` gives `q_j=1_B`.  Hence
`||1_B-p_j||<1`.  Two distinct projections have distance at least one when
one is the unit, so `p_j=1_B`.

This can happen for one selected minimal projection in every matrix summand
only when there is exactly one summand and it is `M_1`; consequently
`D=C1_B`.  But then `dist(x,D)=d>epsilon`, contradicting approximation of
`F`.  No such model exists.
