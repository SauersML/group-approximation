---
rg: 2
id: stw63-robert-sr1-return-proof
kind: route
title: Apply Robert's exact Cu classification of maps from Jiang--Su
target: stw63-sr1-return-is-cu-equality
requires: []
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Approximate unitary equivalence always makes the induced `Cu` maps equal.
For the converse, use Robert, *Classification of inductive limits of
1-dimensional NCCW complexes*, Advances in Mathematics 231 (2012), Theorem
1.0.1.  Its domain is a one-dimensional NCCW complex with trivial `K_1`, a
sequential inductive limit of such algebras, or an algebra stably isomorphic
to such a limit; its codomain is an arbitrary stable-rank-one C-star algebra.
It says that a `Cu_tilde` morphism satisfying the strictly-positive-class
bound is realized by a homomorphism, uniquely up to approximate unitary
equivalence.

The Jiang--Su algebra is a sequential limit of dimension-drop algebras in
that domain class.  Since it is unital, Robert's Theorem 3.2.2(i), used
explicitly at the start of Section 6.3, permits ordinary `Cu` in place of
`Cu_tilde` for classifying its unital homomorphisms.  Therefore equality of
`Cu(phi)` and `Cu(psi)` gives approximate unitary equivalence.  No hypothesis
on the target beyond stable rank one is imported.
