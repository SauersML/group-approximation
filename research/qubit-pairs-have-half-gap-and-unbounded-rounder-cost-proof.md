---
rg: 2
id: qubit-pairs-have-half-gap-and-unbounded-rounder-cost-proof
kind: route
title: Diagonalize the pair and count one indispensable fault at each qubit
target: qubit-pairs-have-half-gap-and-unbounded-rounder-cost
requires: []
artifacts:
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
  - scripts/check_qpcp_rounding.py
---

Section 2 of the artifact is the full proof. The normalized vectors
`(N,-1)` and `(1,N)` diagonalize `P+Q_N` with eigenvalues
`2/(N^2+1)` and `2N^2/(N^2+1)`. Tensor products of this basis diagonalize
the sum, giving normalized ground energy `1/(N^2+1)`.

The two one-qubit kernels have zero intersection. Exactness outside `S`
therefore forces at least one fault at each qubit, even for mixed or
entangled output states, by applying positivity to each reduced density
matrix. Deleting all `Q_N` terms and preparing the all-zero state attains
`|S|=N`. Every rounder on the ground input must consequently satisfy
`N <= C (2N/(N^2+1))`. The same constant preparation works for all inputs at
`C=(N^2+1)/2`, proving sharpness.

These arguments apply to every positive integer `N`. The symbolic and finite
checks are supplementary replay of the explicit algebra, not a substitute
for the universal tensor-product and instrument arguments.
