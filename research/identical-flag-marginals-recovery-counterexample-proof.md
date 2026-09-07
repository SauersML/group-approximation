---
rg: 2
id: identical-flag-marginals-recovery-counterexample-proof
kind: route
title: Compare the odd- and even-parity Bell syndrome states
target: identical-flag-marginals-can-disagree-on-exactifiability
requires: [joint-syndrome-support-characterizes-exactifiability, qubit-pairs-have-half-gap-and-unbounded-rounder-cost]
artifacts:
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
---

Section 3 of the artifact computes all four joint effects. The odd-parity
state assigns `I/2` to each singleton fault label, and the even-parity state
assigns `I/2` to the empty and full labels. Every bit marginal is `I/2`.
The pair's least eigenvalue `2/(N^2+1)` gives the same neighborhood
domination bound for both constructions.

For each singleton label the complementary projector `I-Q_N` or `I-P`
is a normalized state satisfying the retained term. The empty label has
no feasible output. Apply the fixed-measurement support criterion to get
the two different recovery verdicts.
