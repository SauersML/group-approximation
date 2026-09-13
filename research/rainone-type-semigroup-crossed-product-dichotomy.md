---
rg: 2
id: rainone-type-semigroup-crossed-product-dichotomy
kind: claim
title: Rainone's K_0 type semigroup decides stable finiteness and pure infiniteness of reduced crossed products
---

**Theorem (Rainone, *Finiteness and paradoxical decompositions in
C\*-dynamical systems*, J. Noncommut. Geom. 11 (2017); arXiv:1502.06153).**
Let `A` be unital and separable, `Gamma` countable discrete, and
`alpha: Gamma -> Aut(A)` an action.

* **Type semigroup (Definitions 4.6, 4.8; Lemma 4.7).**  When `A` is stably
  finite and `K_0(A)^+` has Riesz refinement, `x ~_alpha y` iff there are
  `u_j in K_0(A)^+` and `t_j in Gamma` with `sum u_j = x` and
  `sum alpha_(t_j)(u_j) = y`.  This is an equivalence relation, and
  `S(A, Gamma, alpha) = K_0(A)^+ / ~_alpha` is a preordered abelian monoid.
* **Stable finiteness (Theorem 4.13).**  For minimal `alpha` and stably finite
  unital `A` with refinement: an invariant faithful tracial state exists
  `<=>` `A rtimes_lambda Gamma` has a faithful tracial state `=>` the crossed
  product is stably finite `=>` `alpha` is completely non-paradoxical `=>` a
  faithful invariant state on `(K_0(A), K_0(A)^+, [1]_0)` exists.  If `A` is
  exact with total projections, the last condition gives back the first.
* **Pure infiniteness from projections (Theorem 4.16).**  If `A` has (SP) and
  `alpha` is minimal and properly outer, then `A rtimes_lambda Gamma` is purely
  infinite iff every nonzero projection of `A` is properly infinite in it.
* **Theorem 4.21.**  For `A` unital, separable, exact, with total projections,
  cancellation and refinement, and `alpha` minimal and properly outer, the
  following conditions satisfy `(1) <=> (2) => (3) => (4) => (5)`:
  1. `S` is purely infinite;
  2. every nonzero element of `K_0(A)^+` is `(k,1)`-paradoxical for some
     `k >= 2`;
  3. the crossed product is purely infinite;
  4. the crossed product is traceless;
  5. `S` admits no nontrivial state.

  If `S` is almost unperforated, then `(5) => (1)`.
* **Dichotomy (Theorems 1.3 and 4.22).**  Under these hypotheses with `S`
  almost (weakly) unperforated, `A rtimes_lambda Gamma` is simple and either
  stably finite or purely infinite.

Rainone notes (page 33) that almost unperforation is more than the proof of
`(5) => (1)` needs.  It suffices that every element `x` with `(k+1)x <= kx`
for some `k` is properly infinite.
