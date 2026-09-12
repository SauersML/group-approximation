---
rg: 2
id: atlas-supercritical-from-pauli-recurrence
kind: route
title: The exact Pauli split plus recurrent finite-state transport is supercritical
target: atlas-supercritical-pauli-branching-cycle
requires:
  - pauli-two-child-transfer-packet
  - strongly-connected-branching-gives-rational-pressure
  - atlas-pauli-branch-recurrence-automaton
---

`pauli-two-child-transfer-packet` gives the fixed positive-trace state `E` and
two exact outgoing branch edges `E -> R_0` and `E -> R_1` with orthogonal
ranges.  `atlas-pauli-branch-recurrence-automaton` adds finitely many fixed
coefficient states and low-energy edges so that the resulting directed
multigraph is strongly connected, while its total wrong-target and incoming
Gram energies are `O(delta^c)`.

The graph is strongly connected and `E` has at least two outgoing edges.
Therefore `strongly-connected-branching-gives-rational-pressure` supplies a
positive integer vector `y` and rational `kappa>0` satisfying

```text
A^T y >= (1+kappa)y.
```

The `E` coordinate of `y` is positive and `tau(E)=1/8`, so the weighted carrier
mass has the fixed lower bound

```text
sum_j y_j tau(P_j) >= y_E/8 > 0.
```

The recurrence claim supplies the required `O(delta^c)` error bound.  These are
exactly the data requested by `atlas-supercritical-pauli-branching-cycle`.
Thus its only new atlas-specific content is finite-state recurrence of the two
already-existing Pauli children.