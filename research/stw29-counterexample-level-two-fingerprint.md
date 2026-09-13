---
rg: 2
id: stw29-counterexample-level-two-fingerprint
kind: claim
title: Rordam's dichotomy fails iff some finite simple real rank zero algebra has an infinite 2x2 matrix algebra, and such an algebra is a non-separative exchange ring
distinct_from:
  stw29-projection-qq-characterizes-rr0-dichotomy: that characterizes the dichotomy by projection-level QQ on V(A); this reduces a counterexample to matrix level two, displays an explicit separativity failure and weak-cancellation failure, and places the counterexample inside the separativity problem for exchange rings.
  stw99-problem-lx-rr0-weak-cancellation: that problem asks for weak cancellation of all real rank zero algebras; this claim shows every counterexample to the dichotomy violates it through the explicit pair [1], [1]+r, and gives the level-two normal form.
---

Call `A` *stably finite* if no matrix algebra over `A` contains an infinite
projection.

**Theorem.**  The following are equivalent.

1. Problem XXIX has a negative answer: some simple C\*-algebra of real rank
   zero is neither stably finite nor purely infinite.
2. There is a unital simple C\*-algebra `C` of real rank zero such that `C` is
   finite while `M_2(C)` is infinite.
3. Statement 2 holds with `C` separable.

Every `C` as in 2 has the following properties.

* (a) `M_2(C)` is properly infinite.  There is an orthogonal sequence of
  nonzero projections `e_1, e_2, ...` in `C` with
  `1_C direct_sum 1_C <~ e_i direct_sum e_i` for every `i`.
* (b) `C` has no nonzero quasitrace (so no tracial state) and infinite
  topological stable rank.
* (c) Let `u = [1_C]` in `V(C)`.  Write `2u = 4u + w` and put `r = 2u + w`.
  Then `x = u` and `y = u + r` satisfy

  ```text
  2x = 2y = x + y,        x != y.
  ```

  Hence `V(C)` is not separative.  It is therefore wild (not tame) by
  `ara-goodearl-tame-refinement-monoids-separative`.  `C` also fails weak
  cancellation: `x + u = y + u`, both `x` and `y` are full, and `x != y`.
* (d) As a ring, `C` is a simple exchange ring that is not separative.  A
  negative answer to XXIX is thus also a negative answer, inside simple
  real-rank-zero C\*-algebras, to the separativity problem for exchange rings
  of Ara--Goodearl--O'Meara--Pardo, which is still open.

For the algebra `A` of statement 1, `V(A) = V(C)`, because `C` is a full corner
of `A tensor K`.  So (a)--(d) also describe the projection monoid of any
counterexample.
