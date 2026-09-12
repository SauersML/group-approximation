---
rg: 2
id: logarithmic-root-gauge-ramp-proof
kind: route
title: Rotate one reflection down a bounded-degree distance ramp
target: bounded-degree-clouds-have-logarithmic-root-gauge-leak
requires: []
---

Let `B=max(2,Delta-1)` and

```text
R=floor((log_B Q)/4).
```

The degree bound gives

```text
|Ball_C(o,R)| <= O_Delta(B^R)=O_Delta(Q^(1/4)).              (BRG4)
```

Put

```text
theta_v=(pi/4) max(1-dist(o,v)/R,0),
W_v=[[cos theta_v,-sin theta_v],[sin theta_v,cos theta_v]],
U_v=W_v Z W_v^*.
```

Every `U_v` is an exact involution.  Adjacent distance levels differ by at
most one, and the map `theta -> W_theta Z W_theta^*` is `2`-Lipschitz in
normalized Hilbert--Schmidt norm.  Hence every edge defect is at most
`pi/(2R)=O_Delta(1/log Q)`.  Outside the radius-`R` ball, `U_v=Z`.  At the
root, rotation by `pi/4` sends `Z` to the Pauli reflection `X`, and

```text
||X-Z||_2=sqrt(2).
```

This proves `(BRG1)--(BRG3)`.  Replacing `Z` by each member of a fixed exact
two-dimensional packet and conjugating all members by `W_v` preserves every word relation
inside one vertex exactly; the same Lipschitz estimate controls overlap
equalities.
