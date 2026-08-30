---
rg: 2
id: kt-q2-double-reduced-unique-trace-proof
kind: route
title: Apply the reduced unique-trace theorem to the trivial radical
target: kt-q2-double-reduced-algebra-has-unique-trace
requires: [kt-q2-double-has-trivial-amenable-radical]
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

The Breuillard--Kalantar--Kennedy--Ozawa theorem says that a discrete group
has trivial amenable radical if and only if its reduced group C-star algebra
has the unique-trace property.  Apply it to the prerequisite.  The canonical
regular trace always exists, so it is the unique tracial state on `C*_r(D)`.

This is the exact scope in which uniqueness is useful: a norm-corona
embedding of `C*_r(D)` induces a trace, and the theorem forces that trace to
be canonical.  Nothing here constructs the embedding.
