---
rg: 2
id: topologically-free-minimal-cantor-action-with-finite-clopen-type
kind: claim
title: Some topologically free minimal action on a Cantor space has no invariant probability measure but a clopen set whose type-semigroup class is finite
distinct_from:
  measure-free-minimal-cantor-action-with-finite-clopen-type: that allows any minimal action and follows from Wehrung's realization theorem with no control of fixed points; this demands topological freeness, which makes the reduced crossed product simple and brings in Rainone's theorems.
  stw99-problem-xxxiii-dynamical-comparison: that asks for dynamical comparison of free minimal amenable actions; this asks for its failure, at a single clopen class, for topologically free minimal actions with no invariant measure.
---

There are a countable group `Gamma` and an action of `Gamma` on a Cantor space
`X` with the following properties.
* The action is minimal and topologically free: for `gamma != 1`, the fixed
  set of `gamma` has empty interior.
* There is no invariant Borel probability measure.
* Some nonempty clopen `A` has a finite class `[1_A]` in `S(X, Gamma)`.

**Status (2026-09-13): established, unreviewed**, by two routes.
* `topologically-free-finite-clopen-type-boldrini-prasad-citation`.  Priority
  belongs to Boldrini--Prasad, arXiv:2607.01896, Corollary 6.12, read with ABBL
  Proposition 2.11.
* `topologically-free-finite-clopen-type-via-generic-witnesses`, a later
  independent proof.
* `refinement-monoids-are-topologically-free-cantor-types` realizes every
  countable simple conical refinement monoid by a minimal topologically free
  action of `F_infinity`, generic among Wehrung's witness tuples.
* The Ortega--Perera--Rordam monoid then gives `[1_X]` finite and `2[1_X]`
  properly infinite, with no invariant measure.
* Open refinements:
  * free actions, in particular of `F_2`
    (`free-minimal-cantor-action-with-finite-clopen-type`);
  * whether the reduced crossed product is then purely infinite
    (`cantor-crossed-product-with-finite-type-is-mixed`).

**Why it matters.**
* A negative answer settles commutative coefficients.  For minimal
  topologically free actions on `C(X)`, Rainone's Theorems 4.13 and 4.21 then
  make `C(X) rtimes_r Gamma` stably finite or purely infinite, as in
  `nowhere-scattered-af-crossed-products-dichotomy-proof`.
* A positive answer is the type-semigroup core of every commutative-coefficient
  crossed-product counterexample to Problem XXIX
  (`af-crossed-product-counterexample-normal-form`, parts 3--5).
* A free example with a finite class answers Rainone's question
  (arXiv:1502.06153, page 33) for its group.  The question asks whether a free
  minimal action of `F_2` can have a type semigroup that is not almost
  unperforated.
* Without topological freeness the answer is yes
  (`simple-refinement-monoids-are-minimal-cantor-types`).  So every possible
  obstruction lives in the fixed-point structure.

## Attempts

These attempts predate the resolution by generic witnesses.

* **Wehrung realizations fix clopen sets.**  The group built in
  `simple-refinement-monoids-are-minimal-cantor-types` lies in `Aut(B, mu)`,
  and its automorphisms extend partial isomorphisms by the identity on a
  complement.
  * Where it dies: a topologically free subgroup may lose `mu`-exhaustiveness,
    which changes the type semigroup.
  * Enlarging `B` so that translates are separated adds clopen sets, and these
    may create compressions.
* **Germ groupoid.**
  * The groupoid of germs of the action is effective and minimal, and it has
    the same type semigroup, since types depend only on the partial maps.
  * If it is Hausdorff, `C*_r` of it is simple and contains `C(X)` as a Cartan
    subalgebra.  That would serve Problem XXIX as well as a crossed product
    does, but it is not a group action.
  * Wehrung's Example 4.9.4 (LNM 2188) is a countable refinement monoid with
    order-unit that is not the type monoid of any fundamental Boolean inverse
    meet-semigroup, so it has no effective Hausdorff ample realization.  It is
    not simple, so the simple mixed case is undecided here.
* **Freeing by profinite extensions (idea, unreviewed).**
  * Let a free group `F` act on `X` through `Gamma`.  Let `Y = lim F/N_k` for
    finite-index normal subgroups `N_k` with trivial intersection.
  * The diagonal action on `X x Y` is free.  It is minimal iff every `N_k` acts
    minimally on `X`.
  * By induction from `N_k`, `S(X x F/N_k, F) ≅ S(X, N_k)`, with the class of
    the whole space going to `[F:N_k] [1_X]`.  Clopen types of `X x Y` form
    the direct limit.
  * So `[1_(X x Y)]` is finite iff `[F:N_k] [1_X]` is finite in `S(X, N_k)`
    for every `k`.
  * Where it dies: the tower needs finite-index subgroups whose type
    semigroups keep ever larger multiples of `[1_X]` finite, while the whole
    group already makes `2[1_X]` properly infinite.  Nothing controls the type
    semigroup of a finite-index subgroup of Wehrung's group.
* **Borel pieces cannot give an example.**  This is the Nadkarni argument
  recorded in `measure-free-minimal-cantor-action-with-finite-clopen-type`.
  Any finiteness must be a clopen obstruction with no Borel analogue.
* **Excluded classes.**
  * Free minimal amenable actions of groups with paradoxical towers
    (`stw99-xxxii-paradoxical-towers-citation`).
  * Groups with a normal infinite cyclic or locally finite subgroup acting
    minimally (`minimal-normal-cyclic-subgroup-cantor-dichotomy`,
    `smoothing-normal-subgroup-cantor-dichotomy`).
* **Orientation formulation (inherited idea).**  Rounding a two-column paradox
  down to one copy is a continuous sourceless orientation problem.
  * Where it dies: a finiteness proof must exclude all compressions, not only
    those built from one paradox.
  * Marks-type determinacy arguments work on full shifts, which carry
    invariant measures.
