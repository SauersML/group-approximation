# STW Problem XII: faithful invariant trace criterion audit

## Result

For every separable unital AH algebra `A` and every automorphism `alpha`,

```text
A rtimes_alpha Z embeds into a unital simple AF algebra
iff A has a faithful alpha-invariant tracial state.
```

Thus every simple quasidiagonal crossed product in Problem XII is
AF-embeddable.  The stronger simple-AF criterion does not use real rank zero
and applies to arbitrary, including outer-aperiodic, automorphisms.

## Structural audit

AH algebras are separable nuclear UCT algebras.  Nuclearity and the UCT
bootstrap class pass to integer crossed products, so the crossed product is
inside the TWW--Gabe--Schafhauser AF-embedding theorem.  Nuclearity makes all
of its traces amenable.  Therefore embedding into a unital simple AF algebra
is equivalent to the existence of a faithful trace on the crossed product.

The canonical expectation is faithful because `Z` is amenable.  A faithful
invariant trace on the coefficient algebra composed with that expectation
is consequently faithful.  In the other direction, restriction of a
faithful crossed-product trace is faithful and invariance follows by
conjugating with the implementing unitary.  These operations prove the
trace equivalence without any simplicity or freeness assumption.

A unital quasidiagonal algebra has a trace by taking a cluster point of
normalized traces on its unital matrix models.  Simplicity makes that trace
faithful.  This proves the stated Problem XII subclass.

## Boundary

Quasidiagonality alone need not supply a faithful trace in a nonsimple
algebra.  More importantly, ordinary AF-embeddability into a nonsimple AF
algebra does not imply that the domain has a faithful trace.  Thus the
faithful-support condition is a sufficient regime for Problem XII, not its
exact remaining obstruction.  This is distinct from the outer-periodic
Floquet and tensor-factor decomposition classes already recorded.
