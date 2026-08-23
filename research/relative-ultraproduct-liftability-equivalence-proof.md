---
rg: 2
id: relative-ultraproduct-liftability-equivalence-proof
kind: route
title: Translate flexible endpoint repair coordinatewise into a lift of the relative ultraproduct homomorphism
target: authenticated-core-union-basin-is-relative-liftability
requires:
  - congruence-endpoint-orbits-are-restriction-ring-fibers
  - exact-torsion-frame-has-rank-one-strict-counterpackets
---

Because all presentation defects of `(X_n,beta_n)` tend to zero, word
evaluation in the tracial ultraproduct makes `(AUL2)` an exact homomorphism.
The core is represented by exact coordinate homomorphisms by hypothesis.

Suppose first that flexible endpoint repair holds.  Choose repaired exact
tuples on dimensions `D_n=d_n+o(d_n)`, together with the almost-full corner
identifications in the definition of the flexible metric.  Every repaired
tuple is an exact finite-dimensional representation of `A`, hence factors
through an odd congruence quotient.  The corner identifications say exactly
that its generator representatives lift `(AUL2)` and its prescribed core.

Conversely, suppose the relative lift exists.  Evaluate its exact
representations on the fixed square-free generators.  By the defining
compression convergence, these exact endpoint tuples are a flexible repair
of `(X_n,beta_n)`.  This proves the equivalence without a quantitative
modulus; standard compactness upgrades qualitative failure to a fixed
positive separated sequence if needed.

For a fixed `n`, two lifts restricting to `beta_n` are in the same
core-commutant orbit exactly when their global multiplicity vectors agree.
This is `(AUL3)`.  The metric estimate for restriction fibers gives the
uniform Selberg normal control after a lift type is chosen.

Finally, the compressed even-Weil sequence in
`exact-torsion-frame-has-rank-one-strict-counterpackets` has no exact lift in
the original dimension but has one after restoring a single deleted line.
Thus replacing `D_n=d_n+o(d_n)` by `D_n=d_n` would make the equivalence
false, while the stated flexible lift retains the known repair mechanism.
