---
rg: 2
id: rr0-c-star-algebras-are-separative
kind: claim
title: Every C*-algebra of real rank zero is separative (AGOR's Problem)
distinct_from:
  stw99-problem-lx-rr0-weak-cancellation: that root has two parts, weak cancellation and K1-surjectivity; this is separativity alone, which gives the root by AGOR (route stw99-lx-via-rr0-separativity) and is implied by the root's first part (route rr0-separativity-via-lx).
  finite-simple-rr0-algebras-have-weak-cancellation: that restricts to finite simple unital algebras, where separativity and weak cancellation coincide and are equivalent to stable rank one; this asks it for all real rank zero algebras.
  stw29-separative-projection-monoid-dichotomy: that derives the dichotomy for simple algebras from separativity of V(A); this asks whether real rank zero forces separativity.
artifacts:
  - research/artifacts/rr0-separativity-prime-reduction-2026-09-16.md
---

Let `A` be a C\*-algebra of real rank zero.  For projections `p, q` in
`M_inf(A)`, must `p direct_sum p ~ p direct_sum q ~ q direct_sum q` imply
`p ~ q`?

This is the Problem of Ara--Goodearl--O'Meara--Raphael (Pacific J. Math. 195
(2000), arXiv:math/9906141, Section 3): "Is every C\*-algebra with real rank
zero separative?"  Since real rank zero C\*-algebras are exactly the exchange
C\*-algebras (AGOP Theorem 7.2, as quoted by AGOR), it is the C\*-case of the
separativity problem for exchange rings.

Status (checked 2026-09-16): open.  STW (arXiv:2506.10902, e-print of
2026-05-11) list it as Problem LX(1).  Ara--Goodearl--O'Meara--Pardo--Perera,
*Regular ring properties degraded through inverse limits* (arXiv:2405.06837,
v2 2024-11-20, abstract read 2026-09-16), call the regular ring version "the
long standing Separativity Problem".  Regular rings and real rank zero
C\*-algebras are both exchange rings, but neither class contains the other
beyond the finite-dimensional case, so an answer for one class does not by
itself settle the other.

## Attempts

* **Reduction to prime algebras** (route
  `rr0-separativity-from-prime-case-and-k1-bijectivity`, artifact).  If every
  unital real rank zero algebra is K1-bijective (Zhang's conjecture), a minimal
  counterexample can be taken unital and prime, with `1 = P + Q`,
  `P direct_sum P ~ Q direct_sum P ~ Q direct_sum Q`, `P` not equivalent to
  `Q`, but `P ~ Q` modulo every nonzero ideal.  Primeness comes from gluing
  partial isometries across a pullback `B/K_1 x_(B/(K_1+K_2)) B/K_2`, where the
  K1 obstruction to gluing is killed by surjectivity on the two sides and
  injectivity on the common quotient.  Conversely separativity gives
  K1-bijectivity (`rr0-k1-bijectivity-via-separativity`), so the problem is
  equivalent to Zhang's conjecture plus the prime case.
* **Simple case.**  For simple unital `A`, separativity of `V(A)` is weak
  cancellation.  It holds for purely infinite simple algebras (Cuntz), and for
  finite simple ones it is equivalent to stable rank one
  (`finite-simple-rr0-sr1-via-weak-cancellation` and
  `finite-simple-rr0-weak-cancellation-via-stable-rank-one`).  A mixed simple
  counterexample would refute Rordam's dichotomy
  (`stw29-counterexample-level-two-fingerprint`).
* **Known positive classes.**  Stable rank one; purely infinite simple;
  extremally rich real rank zero (Brown--Pedersen, as quoted by AGOR); tame
  `V(A)` (Ara--Goodearl, *Tame and wild refinement monoids*; recalled, not
  re-read); inductive limits of separative algebras (separativity passes to
  direct limits of monoids, and `V` commutes with inductive limits); extensions
  of separative real rank zero algebras by separative ideals (AGOP Theorem 7.5,
  cited in AGOR Section 3; not re-read).  Consequently a counterexample has a
  wild `V(A)`, is not an inductive limit of separative blocks, and cannot be
  built as an extension of separative pieces.  None of the sources consulted
  gives a real rank zero realization of a non-separative refinement monoid.
* **Where monoid arguments stop.**  Non-separative refinement monoids exist
  (recalled from the refinement monoid literature, e.g. the discussion of wild
  monoids by Ara--Goodearl; not re-read), so separativity must use analytic
  input from real rank zero beyond refinement.  The prime reduction shows the analytic
  input needed is exactly unitary K-theory (Zhang's conjecture) plus the
  prime case.  In the prime case the ideal lattice is useless for gluing, the
  same wall recorded for LXI in
  `prime-quotient-minimal-k1-trivial-unitaries-are-null`.
