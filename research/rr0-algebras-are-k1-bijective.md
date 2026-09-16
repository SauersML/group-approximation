---
rg: 2
id: rr0-algebras-are-k1-bijective
kind: claim
title: Every unital C*-algebra of real rank zero is K1-bijective (Zhang's conjecture)
distinct_from:
  stw99-problem-lx-rr0-weak-cancellation: that root asks for weak cancellation and K1-surjectivity together; this is the unitary K-theory half alone, stated as bijectivity.
  agor-separative-rr0-algebras-are-k1-bijective: that is the known theorem under separativity; this asks for it with no separativity hypothesis.
  stable-rank-one-unital-algebras-are-k1-bijective: that assumes stable rank one; this assumes only real rank zero.
---

Let `A` be a unital C\*-algebra of real rank zero.  Is the natural map
`U(A)/U(A)° -> K_1(A)` an isomorphism?

This is Zhang's unpublished conjecture as recorded by Ara--Goodearl--O'Meara--
Raphael (arXiv:math/9906141, Section 3): "if A is any unital C\*-algebra with
real rank zero, the topological K_1(A) is isomorphic to the unitary group U(A)
modulo the connected component of the identity".  Injectivity is attributed to
Lin (AGOR cite Lin, Lemma 2.2; STW cite Lemma 2.1 of the same paper; the scanned
paper was not readable here), so the open content is K1-surjectivity, which is
STW Problem LX(2).

## Attempts

* **Via separativity.**  Separative unital real rank zero algebras are
  K1-bijective (`agor-separative-rr0-algebras-are-k1-bijective`), so this claim
  follows from `rr0-c-star-algebras-are-separative`
  (`rr0-k1-bijectivity-via-separativity`).  AGOR's surjectivity proof is ring
  theoretic: separative exchange rings are GE-rings (AGOR Theorem 2.8), so
  `GL_1(A) -> K_1^alg(A)` is onto.
* **The converse direction is not known.**  K1-bijectivity does not obviously
  give separativity.  If `P direct_sum P ~ Q direct_sum P` with `1 = P + Q`,
  the witnessing partial isometry completes to a unitary of `M_2(A)` conjugating
  `P direct_sum P` to `Q direct_sum P`.  K1-surjectivity lets one replace its
  class by that of a unitary of `A`, but that only yields a stabilized
  unitary equivalence, and extracting `P ~ Q` from it is again a cancellation
  statement.  What bijectivity does give is the reduction of separativity to
  prime algebras (`rr0-separativity-from-prime-case-and-k1-bijectivity`).
* **Where a direct attack dies.**  To show a unitary `u` of `M_n(A)` has the
  K1 class of a unitary of `A`, one wants to deform `u` through invertibles of
  `M_n(A)` to some `v direct_sum 1_(n-1)`.  The standard reduction moves the
  last column of `u` to the unit column by elementary row operations, and this
  needs the unimodular last column to be reducible over `A`, which is a stable
  rank condition.  Real rank zero supplies many projections but no such
  reduction by itself.  AGOR get the reduction in the separative case from the
  GE-ring property instead.  Among simple algebras, purely infinite ones are
  covered by Cuntz, and stable rank one is the classical case (AGOR: "e.g., this
  is equivalent to [Rieffel, Theorem 2.10]").  No argument was found for finite
  simple real rank zero algebras without stable rank one.
