---
rg: 2
id: uct-cartan-trivial-k-kirchberg-uct-iff-cartan
kind: claim
title: A unital Kirchberg algebra with trivial K-theory satisfies the UCT exactly when it has a Cartan subalgebra
distinct_from:
  barlak-li-cartan-subalgebras-force-uct: that is the one-way theorem that a nuclear algebra with a Cartan subalgebra satisfies the UCT, with the global Kirchberg-algebra remark; this is the two-way equivalence for a single trivial-K-theory Kirchberg algebra, which turns a counterexample into a Cartan-free algebra.
  trivial-k-theory-kirchberg-algebras-are-o2: that is the open isomorphism question for these algebras; this proves that for each such algebra, being O_2, satisfying the UCT and having a Cartan subalgebra are the same property.
  uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan: that shows the UCT does not give a Cartan subalgebra for type I algebras; this shows that on the trivial-K Kirchberg test class it does.
artifacts:
  - research/artifacts/uct-cartan-obstruction-2026-09-12.md
---

**ESTABLISHED (derivation, this repository).**  Let `A` be a unital Kirchberg
algebra with `K_0(A) = K_1(A) = 0`.  The following are equivalent:

1. `A` satisfies the UCT;
2. `A ≅ O_2`;
3. `A` has a Cartan subalgebra.

Consequently, some separable nuclear C\*-algebra fails the UCT if and only if
some unital Kirchberg algebra with trivial K-theory has no Cartan subalgebra.

Proof: `uct-cartan-trivial-k-kirchberg-uct-iff-cartan-proof`.

**Bearing on the UCT problem.**  A counterexample, taken in Kirchberg's test
class, is exactly a trivial-K Kirchberg algebra with no Cartan subalgebra.  By
`uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan`, absence of a Cartan
subalgebra alone proves nothing outside this class, since it already happens for
type I algebras.

**Credit.**  The global form is Barlak--Li, arXiv:1511.02697v3, Remark 3.3: the
UCT problem has a positive answer iff every Kirchberg algebra admits a Cartan
subalgebra.  For unital simple algebras of finite nuclear dimension, 1 ⟺ 3 is
also X. Li's Corollary 1.4 in arXiv:1802.01190
(`li-simple-finite-nuclear-dimension-cartan-iff-uct`).
The pointwise statement is recorded here without priority claim.
