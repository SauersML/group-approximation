---
rg: 2
id: hyperfinite-ultrapower-trace-not-qd-proof
kind: route
title: Restrict the ultrapower trace to a matrix ultraproduct
target: hyperfinite-ultrapower-trace-not-quasidiagonal
requires: [matrix-tracial-ultraproduct-trace-not-quasidiagonal]
artifacts:
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
---

Fix unital trace-compatible inclusions `M_{2^n} ⊂ R` (the CAR
filtration: `tr_{2^n} = τ_R` restricted).  Coordinatewise they induce a
unital trace-preserving \*-embedding of the tracial matrix ultraproduct
`Q = ∏_ω M_{2^n}/J_HS` into `R^ω`.

Quasidiagonality of a trace passes to unital C\*-subalgebras: a finite
subset of the subalgebra is a finite subset of the ambient algebra, and
the ambient models restrict.  So if `τ_{R^ω}` were quasidiagonal, its
restriction `τ_ω` to `Q` would be quasidiagonal, contradicting the
premise (which covers `k_n = 2^n` and every free `ω`).
