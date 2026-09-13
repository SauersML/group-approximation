---
rg: 2
id: rainone-question-answered-by-generic-witnesses
kind: route
title: Independent proof that a finite clopen class in a measure-free minimal topologically free Cantor system violates almost unperforation and Rainone's weaker condition
target: rainone-non-almost-unperforated-minimal-outer-action-exists
requires: [topologically-free-minimal-cantor-action-with-finite-clopen-type]
---

**Credit.**  The existence of such actions is due to Boldrini--Prasad
(arXiv:2607.01896, Corollary 6.12); see `rainone-question-boldrini-prasad-citation`.
This route was found later and independently, and claims no novelty.

**Step 1: the action.**  `topologically-free-minimal-cantor-action-with-finite-clopen-type`
gives a minimal, topologically free action of a countable group `Gamma` on a
Cantor space `X`.  It has no invariant probability measure, and some nonempty
clopen `A` has a finite class `theta = [1_A]` in `S(X, Gamma)`.

**Step 2: the hypotheses of Theorem 4.22 hold for `C(X)`.**
* `C(X)` is unital, separable and exact.  Its projections are the clopen
  indicators, and they cancel: `K_0(C(X)) = C(X, Z)` with positive cone
  `C(X, Z^+)`, which has Riesz refinement.
* For commutative `C(X)`, properly outer is the same as topologically free.
* "Projections total" is recalled for zero-dimensional `X`, not re-verified.

**Step 3: the type semigroup is the clopen one.**  Rainone's
`S(C(X), Gamma, alpha)` is `K_0^+ / ~_alpha`, where `x ~ y` iff
`x = sum u_j` and `y = sum alpha_(t_j)(u_j)` with `u_j in K_0^+`
(Definitions 4.6, 4.8).  Every `u_j` is a sum of clopen indicators, so this is
the clopen type semigroup `S(X, Gamma)`.

**Step 4: the two conditions fail.**
* `S` is simple and conical by minimality.  It has no nontrivial state,
  because states match invariant measures (Step 6 of
  `simple-refinement-monoids-are-minimal-cantor-types-proof`, for any action).
* By Tarski's theorem, as in Rainone's proof of (5) => (1),
  `(k+1) theta <= k theta` for some `k`.  So `theta` is an "infinite element"
  in Rainone's sense.
* `theta` is not properly infinite: `2 theta <= theta` would give
  `theta + theta' = theta` with `theta' = theta + z != 0`.  So the condition of
  his last sentence fails.
* Almost unperforation also fails.  Rainone's argument (page 32: "Repeating
  this trick we get (k+1)2θ ≤ kθ") gives `(k+1)(2 theta) <= k theta` from
  `(k+1) theta <= k theta`.  Almost unperforation would then give
  `2 theta <= theta`, which is impossible.
* For the same reason `S` is not purely infinite.  With (5) holding, this
  shows (5) => (1) of Theorem 4.21 fails.
