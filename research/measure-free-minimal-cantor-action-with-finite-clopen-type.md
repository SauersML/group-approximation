---
rg: 2
id: measure-free-minimal-cantor-action-with-finite-clopen-type
kind: claim
title: Some minimal action on a Cantor space has no invariant probability measure but a clopen set whose type-semigroup class is finite
distinct_from:
  stw99-problem-xxxiii-dynamical-comparison: that asks for dynamical comparison of free minimal amenable actions; this asks for the failure, at a single clopen set, of the weakest consequence of comparison in the measure-free case, for any minimal action.
  opr-mixed-simple-refinement-monoid: that realizes a mixed simple refinement monoid abstractly; this asks to realize the mixed phenomenon as the clopen type semigroup of a minimal Cantor system.
---

There is a countable discrete group `Gamma` acting minimally on a Cantor space
`X` with the following two properties.

* There is no `Gamma`-invariant Borel probability measure.
* Some nonempty clopen `A subset X` has a *finite* class `[1_A]` in the type
  semigroup `S(X, Gamma) = C(X, N) / ~` (clopen pieces, finitely many
  translates): `[1_A] + eta = [1_A]` forces `eta = 0`.

Equivalently: `S(X, Gamma)` has no nontrivial state but is not purely infinite.
The proof of `coinvariant-tarski-lemma-minimal-nowhere-scattered` shows that
`S(X, Gamma)` is simple and conical, so infinite classes are properly infinite.
By Tarski, `(k+1)[1_A] <= k[1_A]` for some `k`.  So a finite `[1_A]` has an
infinite multiple, and `S(X, Gamma)` fails projection-level QQ.

**Why it matters.**
* This is the type-semigroup core of every commutative-coefficient
  counterexample of crossed-product form
  (`af-crossed-product-counterexample-normal-form`, parts 3--5).
* It is a sharpened form of Rainone's question (arXiv:1502.06153, page 33)
  whether a free minimal action of `F_2` on the Cantor set can have a type
  semigroup that is not almost unperforated.  He notes that the Ara--Exel
  examples of non-almost-unperforated type semigroups are not minimal.
* A negative answer (no such action) would give the dichotomy for all
  properly outer minimal actions on `C(X)`, through Rainone's Theorems 4.13 and
  4.21, as in `nowhere-scattered-af-crossed-products-dichotomy-proof`.

## Attempts

* **The division mechanism does not apply.**  `K_0(C(X)) = C(X, Z)` fails the
  order divisibility of `coinvariant-tarski-lemma-minimal-nowhere-scattered`
  (`af-k0-order-divisible-iff-no-elementary-subquotient`).  Pieces are
  indicator functions and cannot be divided.
* **Rounding formulation.**  Tarski gives `k` clopen partitions of `A` (the
  columns, after refinement) whose translates cover `k+1` copies of `A`.  A
  single-copy compression is an integral selection of pieces across columns.
  The fractional solution (weight `1/k` on every piece) always exists.
  Choosing the best column pointwise is locally constant, but it breaks the
  partition of `A` on the source side.  So the problem is a continuous
  Hall-type rounding problem.
* **Borel pieces cannot give an example.**  By minimality, finitely many
  translates of `A` cover `X`.  So an invariant probability measure for the
  orbit relation restricted to `A` would give an invariant finite measure on
  `X`, which does not exist.  Nadkarni's theorem (1990: an aperiodic countable
  Borel equivalence relation with no invariant probability measure is
  compressible) then makes `A` Borel compressible, hence Borel properly
  infinite, once countably many Borel pieces are allowed.  So any finiteness of
  `[1_A]` must be a genuinely continuous obstruction, tied to finitely many
  clopen pieces.
* **Excluded cases.**
  * Amenable `Gamma`: invariant measures exist.
  * Free minimal amenable actions of groups with paradoxical towers:
    dynamical comparison holds (GGKN, as recorded in
    `stw99-xxxii-paradoxical-towers-citation`).  With no invariant measure it
    gives `A <~ A_1` and `A <~ A_2` for a clopen split `A = A_1 sqcup A_2`, hence
    `2[1_A] <= [1_A]`.
  * Candidates must use non-amenable groups without known paradoxical towers,
    or actions that are not free or not amenable.
* **Where it dies.**  No invariant of clopen sets other than measures is known
  to obstruct compression.  A subshift built to forbid local compression rules
  must be rigid, while freeness from invariant measures needs paradoxical local
  structure, which tends to supply compression rules.  No mechanism is known
  that provides the second without destroying the first.
