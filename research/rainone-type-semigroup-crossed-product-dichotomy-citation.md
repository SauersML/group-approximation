---
rg: 2
id: rainone-type-semigroup-crossed-product-dichotomy-citation
kind: route
title: Rainone 2017, Definitions 4.6 and 4.8, Theorems 4.11, 4.13, 4.16, 4.21, 4.22 and the closing remark
target: rainone-type-semigroup-crossed-product-dichotomy
requires: []
---

Source: T. Rainone, *Finiteness and paradoxical decompositions in
C\*-dynamical systems*, J. Noncommut. Geom. 11 (2017), 791--822,
arXiv:1502.06153v1.  Read from the arXiv PDF on 2026-09-12.  The blanket
assumption on page 4 is that all algebras are separable and unital.

* Definition 4.6: `x ~_alpha y` iff "there exist `{u_j}` in `K_0(A)^+`,
  `{t_j}` in `Gamma`, such that `sum u_j = x` and `sum alpha_(t_j)(u_j) = y`".
  Lemma 4.7 shows it is an equivalence relation when `A` is stably finite and
  `K_0(A)^+` has Riesz refinement, and Definition 4.8 sets
  `S(A, Gamma, alpha) := K_0(A)^+ / ~_alpha`.
* Theorem 4.11 (Tarski): for an abelian monoid with the algebraic ordering,
  "(n+1)theta is not <= n theta for all n" iff "There is a non-trivial state
  nu : W -> [0, infinity] with nu(theta) = 1."
* Theorem 4.13, verbatim hypotheses: "Let A be a stably finite unital
  C\*-algebra for which K_0(A)^+ has Riesz refinement (sr(A) = 1 and RR(A) = 0
  for example). Let alpha : Gamma -> Aut(A) be a minimal action on A."
  Implications `(1) <=> (2) => (3) => (4) => (5)`, and "If A is exact and
  projections are total in A (e.g. RR(A) = 0) then (5) <=> (1)."
* Corollary 4.14: "Let A be a simple, unital, AF algebra and Gamma a discrete
  amenable group. Then any action alpha : Gamma -> Aut(A) is completely
  non-paradoxical."
* Theorem 4.16: "Let (A, Gamma, alpha) be a C\*-dynamical system with A
  separable with property (SP) and Gamma countable and discrete. Assume that
  alpha is minimal and properly outer. Then the following are equivalent:
  (1) A rtimes_lambda Gamma is purely infinite. (2) Every non-zero projection
  p in A is properly infinite in A rtimes_lambda Gamma."
* Theorem 4.21, verbatim hypotheses: "Let A be a unital, separable, exact
  C\*-algebra whose projections are total. Moreover, suppose A has
  cancellation and K_0(A)^+ has the Riesz refinement property. Let
  alpha : Gamma -> Aut(A) be a minimal and properly outer action."  Conclusion:
  "(1) <=> (2) => (3) => (4) => (5). If the semigroup S(A, Gamma, alpha) is
  almost unperforated then (5) => (1) and all properties are equivalent."  In
  the proof of `(5) => (1)`, the assumption is used only to pass from
  `(k+1)2 theta <= k theta` to `2 theta <= theta`.  The `(2) => (3)` step
  invokes Theorem 4.16 and hence property (SP).
* Theorem 4.22: the crossed product "is a simple C\*-algebra which is either
  stably finite or purely infinite", when `S(A, Gamma, alpha)` is weakly
  unperforated.
* Page 33: "Moreover, almost unperforation may be too strong a condition to
  establish (5) => (1) in Theorem 4.21. What is required is that every
  'infinite element' (in the sense that (k+1)x <= kx for some k) is properly
  infinite. This is a priori a weaker condition than almost unperforation."
