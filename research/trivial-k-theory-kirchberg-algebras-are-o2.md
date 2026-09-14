---
rg: 2
id: trivial-k-theory-kirchberg-algebras-are-o2
kind: claim
title: Every unital Kirchberg algebra with trivial K-theory is isomorphic to O_2
distinct_from:
  stw99-problem-ii-nuclear-uct: that asks the UCT for all separable nuclear algebras; this is the single test class a counterexample must reduce to, stated as an isomorphism question about purely infinite simple algebras.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**OPEN.**  Let `A` be a unital Kirchberg algebra (separable, nuclear, simple,
purely infinite) with `K_0(A) = K_1(A) = 0`.  Is `A ≅ O_2`?  By
`kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras` this is equivalent to
Problem II.

**UCT-free restatement.**  Kirchberg--Phillips classification at the level of
KK needs no UCT: unital Kirchberg algebras are isomorphic exactly when they are
KK-equivalent by an element preserving the unit class.  Since `O_2` is
KK-contractible, `A ≅ O_2` if and only if `[id_A] = 0` in `KK(A, A)`.  So the
question is whether vanishing K-theory forces vanishing of the KK-identity for
a purely infinite simple nuclear algebra.

## Attempts

* **K-theory to KK directly.**  The only known bridge from `K_*(A) = 0` to
  `[id_A] = 0` is the UCT itself (Rosenberg--Schochet), so a direct argument is
  circular.  Dies at the start.
* **A Cartan subalgebra.**  A Cartan subalgebra of `A` gives the UCT
  (`barlak-li-cartan-subalgebras-force-uct`), hence `A ≅ O_2`.  Existence of
  Cartan subalgebras or groupoid models in Kirchberg algebras is known only
  under the UCT (X. Li, Invent. Math. 219 (2020); Evington--Sibbel,
  arXiv:2605.30147, principal groupoid models for stable UCT Kirchberg
  algebras).  Dies: circular.
* **Complexity rank.**  Equivalent to
  `trivial-k-kirchberg-algebras-have-complexity-rank-one`; weak complexity rank
  one holds and the intersection algebra is missing (see that node).
* **UHF localization.**  By `coprime-uhf-stabilizations-detect-uct`, `A ≅ O_2`
  if and only if `A ⊗ M_{2^∞} ≅ O_2` and `A ⊗ M_{3^∞} ≅ O_2`; both are again
  trivial-K-theory Kirchberg algebras.  This splits the question into two
  halves but proves neither.
