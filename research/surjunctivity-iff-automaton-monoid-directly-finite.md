---
rg: 2
id: surjunctivity-iff-automaton-monoid-directly-finite
kind: claim
title: A group is surjunctive on an alphabet exactly when its cellular automaton monoid is directly finite
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse in a matrix ring over a modular group algebra into a strict linear automaton; this is the equivalence between surjunctivity and direct finiteness of the monoid of all automata, linear or not.
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

For a group `G` and a finite alphabet `A`, the following are equivalent:

- every injective automaton `A^G -> A^G` is surjective;
- the monoid `CA(G;A)` under composition is directly finite: `sigma o tau = id` implies
  `tau o sigma = id`.

For strict `tau` with a left inverse `sigma`, `E = tau o sigma` is an automaton idempotent different
from `id`. It retracts onto the proper subshift `tau(A^G)`, which is conjugate to the full shift.
The images `tau^n(A^G)` strictly decrease, and `tau` is bijective on their intersection. So a proof
of surjunctivity is exactly a size on `CA(G;A)` that drops on proper retracts:
- sofic counting, for sofic `G`;
- Rokhlin entropy, given a lower bound on Bernoulli Rokhlin entropy;
- nothing yet on nonsofic hosts.

This is the standard reformulation, recorded with proof in Proposition 3.1 of the artifact.
