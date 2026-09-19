---
rg: 2
id: fixed-depth-rank-mesh-proof
kind: route
title: Amplify the rank lattice while keeping the normalized microstate fixed
target: fixed-depth-rank-mesh-has-zero-hs-density
requires:
  - additive-index-instability
  - corner-renormalization-cost
---

All restriction and induction matrices in one fixed finite packet have
rational coefficients with one common denominator `q`.  A nonzero integral
residual can therefore force only `1/(qd)` after normalization by the ambient
dimension.  Iterating a fixed recurrence of depth `m` multiplies this lower
bound by at most the fixed number `lambda^(-m)`.

Now amplify every matrix by `I_k`.  Relator defects, marked distances, and
normalized traces are unchanged, while all ranks and the ambient dimension
are multiplied by `k`; the available lattice spacing in normalized units is
`1/(qkd)`.  Letting `k` tend to infinity proves `(FRM2)`.  If a proposed
comparison retains a fixed positive value under this operation, that value
comes from an extensive density inequality, not from quantization.

