---
rg: 2
id: raz-odd-cycle-repetition-citation
kind: route
title: Import the main theorem of Raz, A Counterexample to Strong Parallel Repetition (FOCS 2008, SICOMP 2011)
target: raz-odd-cycle-repetition-lower-bound
requires: []
---

Literature import, credited in full.

Ran Raz, *A Counterexample to Strong Parallel Repetition*, FOCS 2008;
SIAM J. Comput. 40(3):771--777, 2011. Verified on 2026-09-17 from the author's
PDF (abstract and Section 2):

* Abstract: "we consider the odd cycle game of size m; a two-prover game with
  value 1 − 1/2m. We show that the value of the odd cycle game repeated in
  parallel n times is at least 1 − (1/m)·O(√n)."
* Abstract, item 2: "For parallel repetition of XOR games, unique games and
  projection games: the bounds of (1 − ε^2)^Ω(n) given in [FKO07] (for XOR
  games) and in [Rao07] (for unique and projection games) are tight."
* Introduction: "Since the odd cycle game is a projection game, a unique game,
  and a XOR game, this answers ..."
* Section 2: "the question x is chosen uniformly in {0,...,m−1} and the
  question y is chosen to be: x with probability 1/2, x−1 with probability
  1/4, and x+1 with probability 1/4 ... The predicate V(x,y,a,b) holds if both
  a,b ∈ {0,1} and: if x = y then a = b, and if x ≠ y then a ≠ b. It is easy to
  see that the value of the odd cycle game is 1 − 1/2m."
* Section 2: "Our main result is a probabilistic protocol for the repeated
  game, that achieves a value of 1 − (1/m)·O(√n)" and "the same value can be
  achieved by a deterministic protocol."

The `O(√n)` is uniform in `m` and `n`; this is how the theorem is used in item
2 of the abstract, where `m` and `n` vary together. We name its constant `B`.
`square`
