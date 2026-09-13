---
rg: 2
id: topologically-free-finite-clopen-type-boldrini-prasad-citation
kind: route
title: Boldrini-Prasad Corollary 6.12 with Ara-Bonicke-Bosa-Li Proposition 2.11 gives a finite clopen class
target: topologically-free-minimal-cantor-action-with-finite-clopen-type
requires: []
---

**Sources.**  Both were read from the arXiv PDFs on 2026-09-13.
* P. Boldrini and A. Prasad, arXiv:2607.01896v1 (2 Jul 2026), Corollary 6.12
  (p. 24): "There exist topologically free minimal actions of F_∞ on the Cantor
  space without invariant measures that fail dynamical comparison."
* Ara--Bönicke--Bosa--Li, arXiv:2001.00376v3, Proposition 2.11 (p. 14): "Let G
  be an ample second countable groupoid such that every measure in UM(G) is
  trivial. Then G has dynamical comparison if and only if every element in S(G)
  is properly infinite."

**Deduction.**
* Take an action from BP Corollary 6.12.  It is minimal and topologically free
  on the Cantor space `X`, and it has no invariant probability measure.
* Every invariant Radon measure is 0 or infinite on each nonempty clopen set.
  A finite positive value on one clopen set would be finite on `X`, by
  minimality and compactness, and would normalize to an invariant probability
  measure.
* So ABBL Proposition 2.11 applies to the transformation groupoid.  Since
  comparison fails, some `x in S(X, F_infinity)` is not properly infinite.
* `S` is simple and conical (minimality), and in such a monoid infinite
  elements are properly infinite.  If `x + eta = x` with `eta != 0`, choose `n`
  with `x <= n eta`.  Then `x = x + n eta >= 2x`.  So `x` is finite.
* Write `x = [f]` with `f = sum_i 1_(A_i)` and every `A_i` nonempty.  Then
  `0 != [1_(A_1)] <= x`, and anything below a finite element is finite.  So
  `A = A_1` is a clopen set with a finite type class.

Priority for the existence belongs to BP.  The route
`topologically-free-finite-clopen-type-via-generic-witnesses` is a later
independent proof.
