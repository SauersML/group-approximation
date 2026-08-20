---
rg: 2
id: hs-pcp-boone-via-supercritical-clifford-trigger
kind: route
title: Turn Slofstra's dimension pressure into a same-model self-destroying Boone compiler
target: hs-pcp-boone-compiler
requires:
  - boone-commutator-criterion-for-halting
  - kleene-mipco-self-destroying-game
  - slofstra-subexponential-hyperlinear-profile
  - robust-clifford-capacity-bound
  - two-generator-amitsur-levitzki-dimension-oracle
  - multiplicity-pi-turing-tape
  - quantitative-higman-embedding-with-dehn-control
  - same-model-supercritical-clifford-trigger
artifacts:
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

Use the Boone word for nonhalting survival and the coRE constant-gap verifier
for the control computation.  Slofstra supplies the quantitative template:
self-similar shift/HNN compression, a finite presentation with area control,
and robust Clifford dimension lower bounds.  In particular,
`robust-clifford-capacity-bound` supplies the final exponential capacity
inequality once an all-pairs approximate Clifford homomorphism exists.  The Amitsur--Levitzki
multiplicity tape detects which finite matrix capacity the current model has.

The new trigger is the missing diagonal splice.  Instead of asking a more
accurate *next* model to be larger, it activates enough Clifford generators
inside the current `d`-dimensional model to force a lower bound strictly
larger than `d`.  Its constant normalized-HS transport gives `(HPB2)`;
Boone's exact nonhalting criterion gives `(HPB1)`.  Therefore the
machine-indexed HS--PCP Boone compiler follows.
