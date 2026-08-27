---
rg: 2
id: bounded-cooccurrence-pauli-shield-proof
kind: route
title: Split a distance-two independent set into X and Z sectors
target: bounded-cooccurrence-joint-pvms-do-not-round-globally
requires: []
---

The square of the co-occurrence graph has maximum degree at most `Delta^2`.
Greedy coloring therefore gives a distance-two independent set `S` of size
at least `N/(Delta^2+1)`.  Split `S=S_X sqcup S_Z` as evenly as possible and
put, on one qubit,

```text
Q_x = sigma_X  for x in S_X,
Q_x = sigma_Z  for x in S_Z,
Q_x = I        otherwise.                                  (BCP1)
```

No two members of `S` occur in one context.  Every context consequently
contains at most one nonidentity reflection, so all of its reflections
commute and have a joint PVM.

Write `C=Delta^2+1` and `s=|S|`.  A uniformly random ordered pair
anticommutes exactly when one endpoint lies in `S_X` and the other in `S_Z`.
Since the squared normalized Hilbert--Schmidt norm of
`sigma_X sigma_Z-sigma_Z sigma_X` is `4`, its complete commutator energy is

```text
F(Q)=8 |S_X||S_Z|/N^2.                                     (BCP2)
```

For `N>=2C`, the balanced split and `s>=N/C` give
`|S_X||S_Z|>=N^2/(8C^2)`, proving `(BCJ1)`.

Finally let `P_x` be any commuting reflection table and put
`e_x=||Q_x-P_x||_2`.  Since `[P_x,P_y]=0`,

```text
||[Q_x,Q_y]||_2 <= 2e_x+2e_y,
||[Q_x,Q_y]||_2^2 <= 8(e_x^2+e_y^2).                       (BCP3)
```

Averaging `(BCP3)` gives `F(Q)<=16 E_x e_x^2`.  Combine this
with `(BCJ1)` to obtain `(BCJ2)`.

