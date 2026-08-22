---
rg: 2
id: nonhyperlinear-from-unnamed-fixed-space
kind: route
title: Detect an unnamed returned subspace by finitely many wandering-word moments
target: non-hyperlinear-group
requires:
  - unnamed-fixed-space-wandering-promotion
  - unnamed-positive-density-fixed-space-is-terminal
---

Apply the terminal Fejer-kernel theorem to `u=w^2`.  The square of an
infinite-order word still has infinite order.  The promotion supplies the
model-dependent projections and a fixed positive density, while canonical
microstates make the first finitely many nonzero moments of `u` tend to zero.
Choosing a fixed Fejer order larger than the reciprocal density gives the
contradiction.

