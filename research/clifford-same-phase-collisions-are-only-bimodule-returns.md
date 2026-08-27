---
rg: 2
id: clifford-same-phase-collisions-are-only-bimodule-returns
kind: claim
title: Arbitrarily many same-phase spectral collisions can be pure bimodule returns
distinct_from:
  marked-copy-collision-forces-overlap-mass: that forces positive pairwise projection overlap from total marked density; this shows that even exact same-phase overlap of every pair need not contain any left-action return.
  two-reflection-pressure-does-not-force-localized-commutation: that uses one anticommuting pair to refute a disagreement-to-commutation inference; this realizes the strongest collision input simultaneously for every pair in an arbitrary fixed finite menu.
  uniform-infinite-pauli-packing-impossible: that rules out one coherent infinite approximately anticommuting family in a fixed matrix algebra; this shows why every fixed finite collision menu remains harmless, in a Clifford representation whose dimension grows with the menu.
---

**ESTABLISHED NO-GO.**  For every fixed `m>=2` there is a finite-dimensional
tracial matrix algebra containing projections `P_1,...,P_m` such that every
pair has the same positive collision mass and an exact same-phase bimodule
intertwiner, but no pair has a nonzero common phase carrier.  More precisely,
there are self-adjoint involutions `A_1,...,A_m` satisfying

```text
A_i A_j=-A_j A_i                    (i!=j),                 (CSC1)
P_i=(1+A_i)/2,
tau(P_i)=1/2,        tau(P_iP_j)=1/4.                        (CSC2)
```

For `i!=j`, the collision contraction

```text
X_ij=P_iP_j
```

has

```text
||X_ij||_2^2=1/4,
A_i X_ij=X_ij=X_ij A_j.                                     (CSC3)
```

Thus collision supplies a perfect **left--right** (Hilbert-space bimodule)
return.  Nevertheless

```text
[A_i,A_j]=A_iA_jA_iA_j=-1,
||([A_i,A_j]-1)Y||_2=2||Y||_2                               (CSC4)
```

for every contraction `Y`.  In particular the commutator is maximally
nonreturning on every nonzero carrier, and

```text
Ran(P_i) intersect Ran(P_j)={0}.                             (CSC5)
```

The example survives arbitrary amplification and tensoring with any
independent exact finite packet.

## Consequence for marked-copy collision schemes

The marked collision inequality can force a pair with large
`||P_iP_j||_2`, and a finite spectral partition can additionally force the
two cuts to lie in the same phase bin.  Those facts alone produce only the
bimodule row in `(CSC3)`: the left letter controls the range of `X_ij`, while
the right letter controls its domain.  They do not produce a contraction
returned by left multiplication by a commutator or Britton word.  Passing
from `(CSC3)` to such a left return requires an operation which turns the
right action into a left action--for example a coherent modular swap--or an
additional matrix-only alignment theorem which rules out the Clifford angle.

This remains true for every fixed finite menu.  Complex Clifford matrices of
size `2^floor(m/2)` realize `(CSC1)` for that whole menu.  Hence increasing a
fixed number of marked copies, using a larger fixed phase partition, or
pigeonholing a finite menu of Britton commutators cannot by itself cross a
dimension-independent threshold.  An unbounded coherent family would be
different, but obtaining it from a finite presentation with uniform defect is
exactly the semantic exposure gate in
`finite-presentation-must-expose-whole-module-with-uniform-defect` and
`uniform-infinite-pauli-packing-impossible`.

## Canonical baseline audit

The collision lower bound is a universal tracial projection inequality, so
the canonical regular representation is allowed to carry the same overlap.
The Clifford model shows the sharp local alternative: the overlap may be
stored at principal angle `pi/4`, where it pays no ordinary relation unless a
mixed holonomy/commutation relation is actually imposed.  Imposing that mixed
relation universally either charges the finite Clifford model or collapses
the intended Britton commutator in the group.  Therefore collision is not a
finite-matrix-only discriminator; the missing input is still a genuinely
noncanonical alignment or modular-swap theorem.

