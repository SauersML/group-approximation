---
rg: 2
id: rstar-polymorphism-clone-consists-only-of-projections
kind: claim
title: Every finitary Boolean polymorphism of R-star is a coordinate projection
artifacts:
  - experiments/rstar_fano_geometry.py
distinct_from:
  rstar-fano-ghost-affine-hull-criterion: that classifies which local supports can be safely affinized; this rules out manufacturing such a support by any coordinatewise operation on finitely many R-star assignments.
  central-pinning-forbids-nonlinear-predicates: that concerns joint spectra in one uniquely pinned finite-group sector; this is an all-arities statement about the ordinary Boolean polymorphism clone of the relation.
  rstar-two-retained-coordinates-admit-a-fixed-cap-section: that changes fresh coordinates occurrencewise while retaining at most two old coordinates; this rules out a uniform coordinatewise operation applied to several whole assignments.
---

**ESTABLISHED.**  For every arity `k>=1`, every operation

```text
f:{0,1}^k -> {0,1}                                    (RPC1)
```

which preserves `R_*` coordinatewise is one of the `k` coordinate
projections.

The replayable finite certificate in `experiments/rstar_fano_geometry.py`
enumerates every Boolean operation in arities one, two, and three and finds

```text
arity 1: identity,
arity 2: the two projections,
arity 3: the three projections.                         (RPC2)
```

Now apply the low-arity consequence of Post's classification of Boolean
clones: every Boolean clone strictly larger than the projection clone
contains a nonprojection operation of arity at most three.  Since
`Pol(R_*)` is a Boolean clone and `(RPC2)` contains no such operation,
`Pol(R_*)` is exactly the projection clone.  Notice also that the unary
calculation removes constants and negation, so no essentially-unary escape
is being suppressed.

Consequently no finite number of perfect `R_*` assignments or commuting
copies can be combined by one deterministic coordinatewise Boolean rule to
produce a new assignment with smaller, cap-valued support.  The output of
every preserving rule is literally one input copy.  Convex randomization
over such rules only mixes coordinate projections and does not shrink a
full-support local distribution.

This is a polymorphism no-go, not an operator-algebra universality theorem.
It does not exclude context-dependent noncoordinatewise dilations, a
different perfect trace, or a matrix-specific carrier return.  Those are
exactly the mechanisms left open by FC-char.

