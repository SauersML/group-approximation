---
rg: 2
id: shrunk-matrix-space-unitary-distance-proof
kind: route
title: A unitary must leak the excess dimension outside the image of a shrunk subspace
target: shrunk-matrix-space-unitary-distance
requires: []
---

Let `Y=K(X)` and write `P_X,P_Y` for the orthogonal projections onto `X,Y`.
For every `T in K`, by definition of `Y`,

```text
(1-P_Y) T P_X = 0.                                   (1)
```

For a unitary `U`,

```text
||(1-P_Y) U P_X||_2^2
 = Tr(P_X U^*(1-P_Y)U P_X)/d
 = dim(X)/d - Tr(P_X U^*P_Y U P_X)/d.
```

The last trace is at most `rank(P_Y)=dim(Y)`, because
`P_X U^*P_Y U P_X` is a positive contraction of rank at most `dim(Y)`.
Therefore `(SMS1)` gives

```text
||(1-P_Y) U P_X||_2^2 >= (dim X-dim Y)/d >= gamma.   (2)
```

Using `(1)` and the fact that left/right multiplication by projections
contracts normalized Hilbert--Schmidt norm,

```text
gamma
 <= ||(1-P_Y)(U-T)P_X||_2^2
 <= ||U-T||_2^2.
```

This holds for every `T in K`, proving `(SMS2)`.