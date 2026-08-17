---
rg: 2
id: kl-via-simple-envelope-reduction
kind: route
title: Prove it for two-generator simple coefficients, and the reduction carries it to all groups
target: kervaire-laudenbach-nonsingular-conjecture
requires: [kl-holds-over-two-generator-simple-groups, kl-counterexample-can-be-two-generator-simple]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Immediate from the two prerequisites: if the conjecture failed for some
coefficient group, the second prerequisite would produce a failure over a
two-generator nonabelian simple group, which the first forbids.

## Why both prerequisites are genuinely used

The reduction alone says nothing — it moves a counterexample without
excluding one.  The restricted statement alone says nothing about arbitrary
coefficient groups.  Together they are the conjecture, and the route is an
equivalence rather than a narrowing: this is the sense in which
`kl-holds-over-two-generator-simple-groups` is the whole problem and not a
special case of it.

## What the route is worth

Not a weakening of the hypothesis — the simple case is not easier than the
general one, it is the same one — but a change of shape.  After the
reduction, `kl-simple-failure-leaves-only-the-cyclic-quotient` turns the
conjecture into a statement with no existential quantifier over coefficient
elements: one word, one kernel, proper or not.  Every remaining lane in this
region is an attempt to certify properness, and
`degree-kernel-abelianization-is-infinite-cyclic` already tells us the
certificate cannot be abelian.
