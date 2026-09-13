---
rg: 2
id: machine-center-vanishes-exactly-on-inf-proof
kind: route
title: Letters fix full basis vectors; universal halting drains every full configuration; divergence keeps one alive
target: machine-center-vanishes-exactly-on-inf
requires:
  - kms-minsky-machine-groups-simulate-their-machines
  - kms-group-with-stop-relations-simulates-all-words
  - clocked-search-machine-halts-universally-exactly-on-inf
  - pumped-divergent-minsky-word-lies-in-profinite-kernel
artifacts:
  - research/artifacts/sofic-fp-machine-center-amplifier-2026-09-12.md
---

The full proof is Section 2 of
`research/artifacts/sofic-fp-machine-center-amplifier-2026-09-12.md`.  The group
is `G_0(P(M_e))`, with the stop relations.

1. **Centrality.**  By KMS Lemma 4.9, a full configuration word maps in `Ḡ` to
   `z_(1,u)`, where `u` contains `A_0..A_(K+2)`.  By the automorphism formulas
   (clause 6 of [[kms-minsky-machine-groups-simulate-their-machines]]), every
   letter fixes `z_(1,u)`: `a_j, a_j', A_j` because `u` contains `A_j`, and
   `ã_j, ã_j'` because `u` contains `A_0`.  So `[w(c), y]` lies in `T_0` and
   maps to `1`.  The map `T_0 -> T_1` is injective (clause 3 of
   [[kms-group-with-stop-relations-simulates-all-words]]), so the commutator is
   `1`, and `T_0` is abelian.
2. **INF.**  `M_e` is universally halting
   ([[clocked-search-machine-halts-universally-exactly-on-inf]]) and simple:
   at every nonzero command exactly one command applies.  So every full
   configuration, lifted to `P(M_e)`, reaches command `0`.  Its semigroup word
   is `0`, and by clause 2 of the stop-relation claim its group word is `1`.
3. **FIN.**  The pumped divergent configuration of
   [[pumped-divergent-minsky-word-lies-in-profinite-kernel]] is full.  Lemma C's
   divergent configuration has clock `0`, so the pumped input is `(c; 1, 0)`.
   Its word is `!= 1` and dies in every finite quotient.
