---
rg: 2
id: leavitt-two-relator-corner-peeling-proof
kind: route
title: Peel globally singleton free letters by reversible Tietze moves
target: leavitt-two-relator-corner-peeling
requires:
  - leavitt-degree3-direct-pivot-screen-is-empty
---

Suppose a current relator has the form

```text
R=A x^epsilon B,                 epsilon in {+1,-1},
```

where `x` occurs nowhere else in the current relator family and does not
occur in `A` or `B`.  The equation `R=1` solves `x` as a word in the other
generators.  A reversible Tietze move therefore deletes `x` and `R` without
adding a relation among the remaining generators.  Induction along any
peeling order proves that, when all relators disappear, the presented group
is precisely `D` free-product the free group on the undeleted letters.  This
also proves injectivity of `D`.

For the two unary orbits write their coefficient corners as `H,Y`.  Pivoting
on `H z=1` gives `z=H^(-1)`; the other unary relation becomes
`Y H^(-1)=1`.  All remaining information is the substituted nine-valent
relator.  The preceding Tietze argument applies to these two relators, so an
empty long-corner two-core cannot kill a nonidentity element of `D`.

There is no loopless two-relator counterpattern with fewer than four long
letter incidences and no singleton: each relator is nonempty and every used
letter must have total degree at least two.  With four incidences the minimal
connected bipartite incidence graph is the four-cycle.  Label its two
letters `H,Y`.  The displayed presentation realizes it.  The first relation
sets `Y=H`; the second then reads `H h H^(-1)=1`, equivalently `h=1`.

This last presentation is an abstract sharpness example, not a claim that the
fixed Leavitt packet realizes its two long corners.  That realization is the
remaining algebraic screen.
