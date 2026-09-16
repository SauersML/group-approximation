---
rg: 2
id: prime-rr0-algebras-are-separative
kind: claim
title: Every unital prime C*-algebra of real rank zero is separative
distinct_from:
  rr0-c-star-algebras-are-separative: that asks separativity of every real rank zero algebra; this is the prime unital case, which with Zhang's conjecture is equivalent to it.
  finite-simple-rr0-algebras-have-weak-cancellation: that is the finite simple case, equivalent to stable rank one; this allows prime non-simple algebras and infinite units.
---

Let `B` be a unital C\*-algebra of real rank zero which is prime: any two
nonzero closed two-sided ideals have nonzero intersection.  For projections
`p, q` in `M_inf(B)`, must `p direct_sum p ~ p direct_sum q ~ q direct_sum q`
imply `p ~ q`?

With `rr0-algebras-are-k1-bijective`, this claim gives
`rr0-c-star-algebras-are-separative`
(`rr0-separativity-from-prime-case-and-k1-bijectivity`), and it is a special
case of that claim.  The proof of the reduction only needs the following
special form, for separable `B` if the original counterexample is separable:
`1_B = P + Q` with `P direct_sum P ~ Q direct_sum P ~ Q direct_sum Q` in
`M_2(B)`, `P` not equivalent to `Q`, and `P ~ Q` modulo every nonzero closed
ideal.

## Attempts

* **Simple case.**  Here the quotient hypothesis is vacuous.  If `B` is purely
  infinite simple, separativity holds (Cuntz's weak cancellation).  If `1_B` is
  finite, separativity is equivalent to stable rank one
  (`finite-simple-rr0-sr1-via-weak-cancellation`,
  `finite-simple-rr0-weak-cancellation-via-stable-rank-one`).  A simple unital
  real rank zero algebra that is infinite but not purely infinite would refute
  Rordam's dichotomy and fail this claim
  (`stw29-counterexample-level-two-fingerprint`).  So the simple case of this
  claim already contains Problem XXIX and the finite simple stable rank one
  question.
* **Structure of a minimal counterexample** (artifact, Sections 1--2 and
  Remark 2).  In the
  special form above, `P` and `Q` are full, and `P ~ Q` modulo every nonzero
  ideal.  AGOR Remark 3.2 cites AGOP Theorem 7.5 for: if `I` and `A/I` are
  separative and `A` has real rank zero, then `A` is separative (AGOP not
  re-read).  So for every nonzero ideal `K` of a minimal counterexample, `K` or
  `B/K` is non-separative, even though the specific pair `P, Q` becomes
  equivalent in `B/K`.  Criticality is tied to one pair, so this does not
  propagate to a contradiction.
* **Where the gluing dies.**  The prime reduction glues partial isometries
  over `B/K_1` and `B/K_2` through the pullback over `B/(K_1 + K_2)`.  That needs
  `K_1 ∩ K_2 = 0`, and in a prime algebra no such pair of nonzero ideals exists.
  Gluing over `B/(K_1 ∩ K_2)` produces only an equivalence modulo
  `K_1 ∩ K_2`, which criticality already provides.  The same wall appears for
  LXI in `prime-quotient-minimal-k1-trivial-unitaries-are-null`.
