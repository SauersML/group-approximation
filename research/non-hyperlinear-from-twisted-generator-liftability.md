---
rg: 2
id: non-hyperlinear-from-twisted-generator-liftability
kind: route
title: The Maslov-sector generator liftability assertion already yields the Deligne witness
target: non-hyperlinear-group
requires:
  - maslov-sector-tracial-generator-ucp-liftability
  - twisted-generator-liftability-implies-e3-nonhyperlinear
---

If `maslov-sector-tracial-generator-ucp-liftability` holds as stated,
then by `twisted-generator-liftability-implies-e3-nonhyperlinear` the
twisted fibre `C^*(Sp_4(Z); alpha)` admits no unital *-homomorphism into
any tracial matrix ultraproduct, so the canonical fibre trace of the
Deligne triple cover has no matricial microstates and `E_3` is an
explicit finitely presented non-hyperlinear group.  Equivalently, by
`deligne-sector-gap-is-exactly-nonhyperlinearity`, the mod-three Maslov
defect gap holds.

Note the route's structure: unlike every LLP route, the required
liftability is FIXED-quotient and FIXED-generator, and its truth is
equivalent to the nonexistence of the very homomorphisms it quantifies
over; establishing it is exactly as hard as producing the witness, and
refuting it is exactly exhibiting a matricial model for the twisted
fibre — i.e. hyperlinearity-side evidence.  The route exists to make
that equivalence load-bearing in the graph rather than a hidden trap.
