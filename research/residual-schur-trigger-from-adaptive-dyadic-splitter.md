---
rg: 2
id: residual-schur-trigger-from-adaptive-dyadic-splitter
kind: route
title: Split the residual packet below its matrix atomic scale
target: residual-commutant-supercritical-schur-trigger
requires:
  - schur-flip-rank-is-residual-atomic-granularity
  - constant-hs-groupification-of-residual-dyadic-splitter
---

The splitter activates `r>log_2L` independent flip cells in the residual
factor with uniform loss.  The granularity theorem says their exactified Pauli
algebra would contain a nonzero projection of trace `2^(-r)<1/L`, below the
smallest nonzero trace in `M_L(C)`, equivalently would force `2^r|L` with
`2^r>L`.  Hence the low-energy branch is impossible and every other branch
pays the fixed floor required by the target.

