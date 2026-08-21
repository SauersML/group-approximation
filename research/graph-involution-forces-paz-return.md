---
rg: 2
id: graph-involution-forces-paz-return
kind: claim
title: A graph involution kills a strictly compressed projection source
distinct_from:
  graph-commutator-authenticates-paz-return: that compares return energy with a graph commutator; this uses involutivity and strict compression to kill the source.
  pauli-zero-atom-removes-acceptance-source-deficit: that provides a Gram vector; this theorem requires a projection on the verifier space.
  controlled-reflection-cell-has-free-orientation: that concerns obtaining the intended compression; this starts after it is obtained.
---

Let `G` be a projection, `W` a unitary, and suppose
`||GWG||_op<=rho<1`.  For the graph commutator `C` of the preceding claim,
if `C` is a self-adjoint involution then `G=0`.  Quantitatively, if an exact
involution `Y` satisfies `epsilon=||C-Y||_2`, then

```text
tau(G) <= epsilon^2/[b^2(1-a^2)],
a=(1+rho)/2, b=(1-rho)/2.
```

This is a complete projection-level theorem.  Its use for PAZ remains
conditional on a positive-density projection decoder for the presently
one-vector Gram source.
