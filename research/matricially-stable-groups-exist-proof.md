---
rg: 2
id: matricially-stable-groups-exist-proof
kind: route
title: Freeness gives the representation outright, and one near-unitary rounds
target: matricially-stable-groups-exist
requires: []
artifacts:
  - GroupApproximation/Sofic/MatricialStabilityInstances.lean
---

## Why sufficient

Two elementary arguments, chosen because each is provable in this repository
from scratch rather than cited.

**Free groups.**  No repair is needed at all.  Given an operator-norm almost
representation `B`, define the genuine representation on the `n`-th model by
the universal property, sending each generator `a` to `B.map n (of a)` — the
almost representation's own value.  The two then agree exactly at every
generator, so the tracking error there is zero, and it propagates along words
because the operator norm is bi-invariant under unitaries: multiplying by a
unitary on either side moves nothing.  Formally the propagation is the
induction `FreeGroup.induction_on`, whose three inductive cases are closure of
tracking under products and inverses and the trivial case at `1`.

That is the whole proof.  No averaging, no functional calculus, no Følner set.

**The integers.**  A homomorphism from `Multiplicative Z` is determined by one
unitary, so stability reduces to rounding a single near-unitary to an exact one
without moving it far.  Take the image of the generator and use its unitary
part; powers then track because the error accumulates linearly and the
tolerance is chosen against the fixed word length.

## What it costs

Nothing external.  Endpoints are
`MatricialStabilityInstances.freeGroup_isPointNormMatriciallyStable` and
`multiplicativeInt_isPointNormMatriciallyStable`, with the resulting radical
computations recorded beside them.  Both are zero-input.

## What it deliberately does not attempt

Stability for amenable groups, which in the literature runs through
quasidiagonality and is not formalized here.  The two classes above are enough
to inhabit the predicate, which is the entire purpose: the manuscript's
stability clauses needed one instance, not a general theory.
