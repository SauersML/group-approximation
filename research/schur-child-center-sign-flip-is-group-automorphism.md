---
rg: 2
id: schur-child-center-sign-flip-is-group-automorphism
kind: claim
title: One ordinary child-group automorphism flips the corrected Schur child center
distinct_from:
  raw-schur-generator-is-not-child-center: that shows the raw last generator does not itself label child simples; this acts on the raw generator in a way which flips the genuine corrected center.
  groupify-schur-child-center-chart: that asks for a complete projection atlas, selector reset, and return; this solves only the two-branch flip and balance inside each fixed selector sector.
  branch-controlled-pauli-selector-reset: that uses raw spectral controls and therefore balances the wrong decomposition; this permutes the actual child-simple types without naming their central projections as group words.
---

Let `A_f<=B_f` be a Schur--Clifford predicate packet and put

```text
C_f=B_f^Q=<A_f,q_*>,                       q_*=q_(N+1).
```

There is an involutive group automorphism `theta_f` of `C_f` given on the
packet generators by

```text
theta_f(a)=a              (a in A_f),
theta_f(q_*)=J q_*.                                          (SCA1)
```

On the `J=-1` sector of the finite group algebra, its linear extension sends
the corrected child-center coefficient of `(RSC2)` to its negative:

```text
theta_f(Q_f)=J Q_f=-Q_f.                                    (SCA2)
```

Consequently `theta_f` exchanges the two genuine `C_f`-simple types over
every fixed selector character. In particular, in the finite semidirect
product

```text
R_f=C_f semidirect_(theta_f) C_2
   =<C_f,s | s^2=1, sgs^(-1)=theta_f(g) (g in C_f)>,          (SCA3)
```

the two corrected child types over each selector character occur with equal
multiplicity in the restriction of every exact `J=-1` representation of
`R_f`.

For approximate representations, exactification of the fixed finite table
`R_f`, followed when necessary by polar alignment on the common `C_f`, bounds
the normalized weighted `L1` imbalance of these paired child types by
`C sqrt(E)`, with `C` depending only on the fixed predicate packet.

This removes the need to turn the nonlinear group-algebra element `Q_f` into
a literal group word merely in order to exchange its signs. It does **not**
reset the old selector character `x`: `(SCA1)` fixes every `z_i`. A recurrent
BCS atlas must still repartition or transport the complete `(x,+/-)` type
vector without a stationary finite-graph-of-groups escape.
