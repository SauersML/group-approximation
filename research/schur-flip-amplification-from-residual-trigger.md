---
rg: 2
id: schur-flip-amplification-from-residual-trigger
kind: route
title: Factor off recovered Pauli capacity and diagonalize against the residual spectator
target: compressor-amplifies-schur-flip-cocycle-rank
requires:
  - schur-flip-cells-expose-residual-matrix-tape
  - residual-commutant-supercritical-schur-trigger
---

Exactify any initial recovered cells and apply `(RMT1)`.  The residual trigger
produces `r>log_2L` new independent cells in their commutant.  Their direct
sum with the old cocycle form has rank `2(n+r)`, while `m=2^nL`; equivalently
`n+r>log_2m`.  Exact residual divisibility makes the low-energy branch
impossible, and all other branches pay the universal
energy floor required by the target.
