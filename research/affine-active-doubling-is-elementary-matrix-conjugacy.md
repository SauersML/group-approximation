---
rg: 2
id: affine-active-doubling-is-elementary-matrix-conjugacy
kind: claim
title: One affine active coefficient copy is elementary-conjugate to two diagonal copies
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out turning a restriction-multiplicity change into the same next packet by plain type-preserving conjugacy; this gives an explicit conjugacy from one coefficient corner to a different two-slot diagonal corner inside a properly infinite matrix algebra.
  affine-leavitt-steinberg-mark-is-fd-invisible: that proves exact finite-dimensional collapse after using all Steinberg root relations; this isolates the explicit ordinary matrix word implementing the one-to-two coefficient placement.
---

Put `R=L_A^c(S)`. In `M_3(R)` define

```text
E=diag(A,0,0),                  F=diag(0,A,A),
X=s_0 E_(1,2)+s_1 E_(1,3),     Y=t_0 E_(2,1)+t_1 E_(3,1). (AEC1)
```

The relative Leavitt relations give

```text
XY=E,                 YX=F.                              (AEC2)
```

In `M_2(M_3(R))=M_6(R)` put

```text
W=[[1-E, X],[-Y,1-F]].                                   (AEC3)
```

Then `W` is invertible and is explicitly elementary:

```text
W=[[1,X],[0,1]] [[1,0],[-Y,1]] [[1,X],[0,1]].             (AEC4)
```

Its inverse is `[[1-E,-X],[Y,1-F]]`. For every `a in AS`, let
`a_hat=aE_(1,1) in M_3(R)`. Coefficient centrality gives

```text
Y a_hat X=diag(0,a,a),                                   (AEC5)
```

and direct multiplication gives

```text
W diag(a_hat,0) W^-1=diag(0,diag(0,a,a)).                 (AEC6)
```

Thus one active coefficient copy is carried by one explicit ordinary
elementary word to two diagonal active copies. Equivalently, for the finite
unit group `G=(AS)^x`, conjugation sends

```text
a |-> 1-E+a_hat
```

to the diagonal two-copy embedding supported on `F`.

This closes the exact word-level proper-corner placement problem. It does
not by itself produce normalized-HS collapse: when only the finite source,
two finite target copies, and this conjugacy are retained, the resulting
chart is a graph of finite groups and has stationary finite-dimensional
representation flows.
