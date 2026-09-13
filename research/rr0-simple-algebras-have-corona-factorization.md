---
rg: 2
id: rr0-simple-algebras-have-corona-factorization
kind: claim
title: Every separable simple real rank zero C*-algebra has the corona factorization property
distinct_from:
  stw99-problem-xxix-rr0-dichotomy: that asks only for the stably-finite/purely-infinite dichotomy; this asks for the corona factorization property, which implies the dichotomy by Ortega-Perera-Rordam Corollary 5.16 and is strictly stronger a priori.
  stw99-problem-lx-rr0-weak-cancellation: that asks for weak cancellation (separativity) of real rank zero algebras; this asks for a comparability property of V(A) of a different shape (monoid CFP), with no cancellation content.
---

Let `A` be a separable simple C\*-algebra of real rank zero.  Does `A` have the
Corona Factorization Property, i.e. is every full projection in
`M(A tensor K)` properly infinite?  Equivalently (Ortega--Perera--Rordam,
Theorem 5.8(ii)), does `V(A)` have the monoid CFP?

This is the simple case of the problem stated by Ortega, Perera and Rordam
(arXiv:0904.0541, page 20): "It is an open problem if all C\*-algebras of
real rank zero have the CFP."  A positive answer settles STW Problem XXIX
(route `stw29-via-rr0-corona-factorization`).

## Attempts

* Monoid axioms alone cannot decide it.  Ortega--Perera--Rordam
  (`opr-mixed-simple-refinement-monoid`) exhibit a simple conical refinement
  monoid with a finite order unit `u` and `2u` properly infinite; such a monoid
  fails the CFP.  Any proof must therefore use input from the C\*-algebra
  beyond Riesz refinement of `V(A)` (and beyond weak divisibility, which is
  automatic for simple conical refinement monoids other than `Z^+`, OPR
  Corollary 2.7).
* The known CFP failures in simple algebras (Rordam's non-stable algebra with
  a stable matrix algebra, and Rordam's finite/infinite algebras) come from
  Euler-class obstructions over infinite products of spheres.  Rordam's
  Villadsen-style argument shows that these algebras are not of real rank zero
  (`rordam-mixed-examples-not-real-rank-zero`): the finiteness certificate
  survives restriction to the zero set of a generic self-adjoint perturbation,
  so a sign-changing coordinate function cannot be approximated by invertibles.
  A real-rank-zero CFP failure needs an obstruction that dies on every generic
  zero set while still blocking proper infiniteness; no such mechanism is
  known.
* Stable rank one with weakly unperforated `K_0` already gives the CFP for
  simple real-rank-zero algebras (Kucerovsky--Ng, as listed in OPR, page 2);
  this covers only the stably finite side, so the mixed case remains fully
  open.
