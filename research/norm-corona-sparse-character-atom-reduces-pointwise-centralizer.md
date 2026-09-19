---
rg: 2
id: norm-corona-sparse-character-atom-reduces-pointwise-centralizer
kind: claim
title: A sparse global character atom can reduce its countable pointwise centralizer
distinct_from:
  norm-corona-sparse-global-character-atom: that selects a possibly rank-one global atom but imposes no invariance on its internal multiplicity space; this selects the full moving cylinder atom slowly enough to commute with a prescribed countable centralizer.
  maximal-sparse-character-atom-does-not-return-multiplicity: that rules out a coordinatewise maximal-rank return argument; this supplies reducing invariance only and makes no rank-maximality or same-reservoir assertion.
artifacts:
  - research/norm-corona-sparse-character-centralizer-proof.md
---

Let `A` be a countable elementary abelian `2`-group and

```text
rho:A -> U(Q),
Q=(product_n M_(d_n)(C))/(directSum_n M_(d_n)(C)).
```

Let `B={b_0,b_1,...}` be a countable family of unitaries in `Q` which
commutes pointwise with `rho(A)`.  If `rho(a_0)!=1`, then there are a nonzero
projection `P in Q` and a character `chi:A->{+1,-1}` such that

```text
rho(a)P=chi(a)P                 for every a in A,       (SCR1)
chi(a_0)=-1,                                            (SCR2)
[P,b]=0                            for every b in B.    (SCR3)
```

The projection may have rank one or vanishing normalized rank along its
nonzero coordinates.  No trace or density hypothesis is used.

For the binary-Leavitt Heisenberg subsystem, take `A` to be the common
central root group.  The two Morita branch actors fix `A` pointwise, and the
two branch Heisenberg images commute with it.  Therefore a surviving marked
central root has a nonzero global character projection which is one common
reducing carrier for both branch actors and the whole countable self-copy
subsystem.

This does not return coefficient multiplicity.  On the common carrier the
two branch representations can still occupy independent UHF-type tensor
coordinates, so the selected projective module has not yet acquired a
unital action of the Leavitt coefficient ring.

