---
rg: 2
id: unfolding-tensor-clauses-returns-the-original-gap-proof
kind: route
title: Dominate clauses by factors, use walk stationarity, and read the loss off BMVZ soundness
target: unfolding-tensor-clauses-returns-the-original-gap
requires: [bmvz-iterable-tensor-gap-amplification, qubit-pairs-have-half-gap-and-unbounded-rounder-cost]
artifacts:
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
---

## Why sufficient

- **(UF1)** Put `Q_j=(Pi_(f(j)))_(copy j)`. These are commuting projections. The
  product `prod_j(I-Q_j)` is annihilated by each `Q_j`, so
  `Q_j(I-prod_i(I-Q_i))=Q_j`. A projection dominates every subprojection, hence
  every convex combination of them. Average over `f` and `chi`.
- **(UF2)** The start vertex of a uniform walk on a `d`-regular graph is uniform,
  and the uniform distribution is invariant under the transition matrix
  `P=A/d` (Lemma 2.10 of arXiv:2510.01333 uses this `P`). So each coordinate is
  uniform, and `E_f Q_j=(H_chi)_(copy j)`.
- **(UF3)** The operators `H_(copy j)` act on distinct tensor factors and have
  the common spectrum of `H`, so the least eigenvalue of their sum is
  `t lambda_min(H)`.
- **(UF4)** (RED1) gives `lambda_min(U_(2t)(H))>=c lambda_min(H^(2t))`. By (UF3)
  the left side is `lambda_min(H)`. In the binding regime,
  `lambda_min(H^(2t))>=eta sqrt(t/log t) lambda_min(H)` (BMVZ (6.66), recorded
  in `bmvz-iterable-tensor-gap-amplification`). Divide by
  `lambda_min(H)>0`. The projector pairs of
  `qubit-pairs-have-half-gap-and-unbounded-rounder-cost` give `P` terms on
  distinct qubits, which commute, and `Q_N` terms on distinct qubits, which
  commute: two layers of equal weight. Their ground energy `1/(N^2+1)` tends to
  zero, which places them in the binding regime `eta sqrt(t/log t) lambda_min(H)<=(1/3)log t/t`
  for large `N`. For `c>0` choose `t` with `sqrt(log t/t)/eta<c`, a
  contradiction.

Section 4 of the linked artifact.
