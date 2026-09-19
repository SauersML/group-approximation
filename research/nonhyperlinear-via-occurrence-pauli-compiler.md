---
rg: 2
id: nonhyperlinear-via-occurrence-pauli-compiler
kind: route
title: Decode occurrence-local Pauli tests and choose the witness size after the matrix dimension
target: non-hyperlinear-group
requires:
  - finite-orbit-occurrence-pauli-compiler
  - occurrence-local-dimension-games-force-mark-collapse
---

The compiler supplies the hypotheses of the occurrence-game collapse theorem
with `D_N->infinity` and a nontrivial common mark.  Apply that theorem to get
a fixed normalized-HS mark-collapse threshold, contradicting canonical-trace
microstates for the nontrivial mark.
