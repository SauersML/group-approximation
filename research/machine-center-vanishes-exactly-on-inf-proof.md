---
rg: 2
id: machine-center-vanishes-exactly-on-inf-proof
kind: route
title: Letters fix full basis vectors; universal halting drains every full configuration; divergence keeps one alive
target: machine-center-vanishes-exactly-on-inf
requires:
  - kms-minsky-machine-groups-simulate-their-machines
  - clocked-search-machine-halts-universally-exactly-on-inf
  - pumped-divergent-minsky-word-lies-in-profinite-kernel
artifacts:
  - research/artifacts/sofic-fp-machine-center-amplifier-2026-09-12.md
---

The full proof is Section 2 of
`research/artifacts/sofic-fp-machine-center-amplifier-2026-09-12.md`.

1. **Centrality.**  By KMS Lemma 4.9, a full configuration word maps in `Ḡ` to
   `z_(1,u)`, where `u` contains `A_0..A_(K+2)`.  By the automorphism formulas
   (clause 6 of [[kms-minsky-machine-groups-simulate-their-machines]]), every
   letter fixes `z_(1,u)`: `a_j, a_j', A_j` because `u` contains `A_j`, and
   `ã_j, ã_j'` because `u` contains `A_0`.  So `[w(c), y]` lies in `T` and maps
   to `1`.  By Lemma 4.14 it is `1`, and `T` is abelian.
2. **INF.**  `M_e` is universally halting
   ([[clocked-search-machine-halts-universally-exactly-on-inf]]) and simple:
   at every nonzero command exactly one command applies.  So every full
   configuration, lifted to `P(M_e)`, reaches command `0`.  By the simulation
   theorem its word equals the stop word, which maps to `z_(1,0) = 1` and is
   trivial.
3. **FIN.**  The pumped divergent configuration of
   [[pumped-divergent-minsky-word-lies-in-profinite-kernel]] is full.  Its word
   is `!= 1` and dies in every finite quotient.
