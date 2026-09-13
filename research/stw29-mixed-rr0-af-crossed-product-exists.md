---
rg: 2
id: stw29-mixed-rr0-af-crossed-product-exists
kind: claim
title: Some minimal properly outer action on a unital AF algebra has a real rank zero reduced crossed product that is neither stably finite nor purely infinite
distinct_from:
  stw29-rr0-mixed-simple-algebra-exists: that is the general negation of Problem XXIX; this is the zero-dimensional crossed-product design for it, whose constraints are proved in af-crossed-product-counterexample-normal-form.
---

There are the following data:

* a unital separable AF algebra `D`;
* a countable discrete group `Gamma`;
* a minimal, properly outer action `alpha: Gamma -> Aut(D)`.

For these, the simple algebra `D rtimes_lambda Gamma` has real rank zero and is
neither stably finite nor purely infinite.

Its truth would settle Problem XXIX negatively (route
`stw29-mixed-via-af-crossed-product`).  It is the zero-dimensional design shape
that the brief of this lane targets, including shapes like Rordam's nuclear
`D rtimes Z` with AF coefficients.

## Attempts

* **Coefficients without elementary subquotients: dead.**  Every such `D`
  gives a dichotomous crossed product (`nowhere-scattered-af-crossed-products-dichotomy`,
  proved, unreviewed).  This covers UHF, simple AF, `C(X) tensor UHF` with
  arbitrary actions, and non-simple AF algebras with any ideal lattice.  For
  `Z`, the non-unital version is in
  `nowhere-scattered-af-integer-crossed-products-dichotomy`.
* **Amenable groups: dead** for unital `D`, because an invariant tracial state
  always exists and is faithful by minimality.
* **Normal form of what survives** (`af-crossed-product-counterexample-normal-form`).
  * `D` has an elementary subquotient, for example `D = C(X)` for a Cantor space.
  * `Gamma` is non-amenable, and there is no invariant tracial state.
  * The coefficient type semigroup has no state, is not purely infinite, is
    not separative, and contains the class of a projection of `D` that is finite
    in the crossed product and has a properly infinite multiple.
* **Commutative coefficients.**  The type-semigroup part is exactly
  `measure-free-minimal-cantor-action-with-finite-clopen-type`.  Free minimal
  amenable actions of groups with paradoxical towers are excluded.  Where this
  dies: no construction of a measure-free minimal Cantor system with a finite
  clopen class is known.  Even with one, finiteness of `1_A` in
  `C(X) rtimes_lambda Gamma` is not implied.  Rainone's Proposition 4.17 only
  detects infiniteness through partial isometries with coefficients in
  partial isometries of `D`.
* **Finiteness certificates.**  A counterexample has no quasitrace on its
  finite corner (`stw29-counterexample-level-two-fingerprint`).  So finiteness of
  `p` cannot come from traces or from `K_0`.  The certificate must be
  non-tracial, like Rordam's Euler classes, which live in non-zero-dimensional
  building blocks.  No non-tracial finiteness certificate for projections in
  crossed products of zero-dimensional algebras is known.  This is where the
  design dies at present.
* **Real rank zero.**  No mechanism is known that gives real rank zero for a
  crossed product that is not purely infinite and has no trace.  Real rank
  zero of the coefficients is automatic but does not pass to the crossed
  product in general.
