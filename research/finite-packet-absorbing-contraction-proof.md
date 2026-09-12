---
rg: 2
id: finite-packet-absorbing-contraction-proof
kind: route
title: Test the contraction chain on the negative regular summand
target: finite-packet-cannot-realize-absorbing-contraction
requires:
  - finite-depth-contractive-computation-ladder
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

Because `J` is a nontrivial central involution, `Q_J=(1-J)/2` is a nonzero
central projection in `C[H]`.  Its range in the left regular representation
is invariant and `J` acts there as `-I`.  Apply all zero-error inequalities in
`(FPC1)` to this finite-dimensional representation and iterate:

```text
a_*<=a_0<=lambda a_1<=...<=lambda^m a_m<=lambda^m A.
```

This contradicts the absorbing-depth choice.  Equivalently, the common
multiple of regular representations from
`finite-packet-graph-atlases-have-a-regular-stationary-flow` supplies the
same counterexample when the proposed finite cell is presented as several
finite vertex packets and ordinary subgroup incidences.

