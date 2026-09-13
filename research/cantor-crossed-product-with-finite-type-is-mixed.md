---
rg: 2
id: cantor-crossed-product-with-finite-type-is-mixed
kind: claim
title: For some minimal topologically free measure-free Cantor action with a finite clopen type class, the reduced crossed product is neither stably finite nor purely infinite
distinct_from:
  topologically-free-minimal-cantor-action-with-finite-clopen-type: that is the type-semigroup statement, established; this asks whether the clopen-level finiteness survives in the reduced crossed product.
  stw29-mixed-rr0-af-crossed-product-exists: that also demands real rank zero and allows AF coefficients; this asks only for a mixed simple crossed product with Cantor coefficients.
---

There is a minimal, topologically free action of a countable group `Gamma` on
a Cantor space `X`, with no invariant probability measure and a finite clopen
type class.  For it, `A = C(X) rtimes_r Gamma` is neither stably finite nor
purely infinite.

**What is known about the candidates.**  Take the actions of
`refinement-monoids-are-topologically-free-cantor-types` for the countable part
of the Ortega--Perera--Rordam monoid, so that `[1_X] = u` and `2u` is properly
infinite.  Then:
* `A` is simple, by minimality and topological freeness (Archbold--Spielberg,
  recalled);
* `A` is exact and has no tracial state;
* `1_X direct_sum 1_X` is properly infinite, so `A` is not stably finite.

By Rainone's Theorem 4.16 (for `C(X)`: property (SP), minimal, properly outer),
`A` is purely infinite iff every clopen projection is properly infinite in
`A`.  So the claim for this candidate says exactly that some clopen projection
is not properly infinite in `A`.  It would follow if `1_X` were finite in `A`.

**Why it matters.**
* It would give a simple exact algebra with a finite and an infinite
  projection, containing a Cantor `C(X)` as a masa with a conditional
  expectation.
* With real rank zero as well, it gives
  `stw29-mixed-rr0-af-crossed-product-exists`, and Problem XXIX fails through
  `stw29-mixed-via-af-crossed-product`.
* A negative answer for all such actions would show that clopen-level
  finiteness never survives analytically.  That would be a comparison theorem
  beyond the type semigroup.

## Attempts

* **Type-semigroup finiteness does not transfer by itself.**
  * The map `S(X, Gamma) -> V(A)` can identify more classes.
  * Rainone's Proposition 4.17 detects infiniteness only through partial
    isometries whose coefficients are projections of `C(X)`.
  * A finite `[1_X]` excludes compressions of `X` by finitely many clopen
    pieces and group elements, not arbitrary isometries in `A`.
* **Traces and `K_0` cannot certify finiteness.**  `A` has no trace.
  * A counterexample's finite corner has no quasitrace
    (`stw29-counterexample-level-two-fingerprint`).
  * In the monoid, `2u + (2u + w) = 2u`, so the nonzero class `2u + w` dies in
    the Grothendieck group.
* **Conditional expectation.**  Let `E: A -> C(X)` be the canonical faithful
  expectation.  If `v*v = 1_X` and `vv* = p < 1_X`, then `E(p)` is a positive
  function below `1_X` with `E(1_X - p) != 0`.
  * Where it dies: without an invariant state nothing sums these defects to a
    contradiction.
  * A rounding argument would move `v` toward a clopen-piecewise partial
    isometry, which is excluded.  Approximating by the algebraic crossed
    product loses the isometry property exactly where rounding is hard, the
    Borel/clopen gap of the Nadkarni contrast.
* **Tame algebras are excluded.**
  * `V(A)` must be non-separative
    (`stw29-separative-projection-monoid-dichotomy`).
  * So `A` is not an inductive limit of algebras with separative `V`, and no
    finite-stage groupoid approximation whose monoids are tame can certify
    finiteness.
