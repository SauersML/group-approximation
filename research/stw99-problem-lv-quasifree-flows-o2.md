---
rg: 2
id: stw99-problem-lv-quasifree-flows-o2
kind: claim
title: Classify the positive-parameter quasifree flows on the Cuntz algebra O2 (STW Problem LV)
root: true
artifacts:
  - research/artifacts/stw99-actions-classification-cluster-2026-08-30.md
---

**Problem LV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Determine when the quasifree flows `α^{(λ)}` on `O_2`
(`s_1 ↦ e^{it}s_1`, `s_2 ↦ e^{iλt}s_2`) are cocycle conjugate, for
irrational `λ > 0`.  For irrational `λ < 0` the flow is Rokhlin
(Kishimoto) hence unique; for `λ > 0` the crossed product is stably
projectionless with a unique tracial ray, and Dean: for GENERIC
irrational `λ > 0` it is `W ⊗ K` (open for all `λ`).

## Attempts

* The natural invariant candidates: the crossed product with its dual
  trace-scaling flow (KMS data — the KMS`_β` structure of quasifree
  flows is classical and depends on `λ` through the Perron root
  equation `e^{-β} + e^{-λβ} = 1`, giving a `λ`-dependent inverse
  temperature).  Since cocycle conjugacy preserves the crossed
  product with its dual action AND rescales KMS temperatures only by
  flow rescaling — which is not available inside cocycle conjugacy
  for fixed parametrization — the unique `β(λ)` solving the Perron
  equation is a cocycle-conjugacy invariant.  `β(λ)` is injective in
  `λ ≥ 1` up to the symmetry `λ ↔ 1/λ` (relabelling the generators
  swaps them after time rescaling... which cocycle conjugacy does NOT
  permit, only conjugacy of reparametrized flows would).  Recorded
  conjecture: `α^{(λ)} ≃_{cc} α^{(μ)}` iff `μ = λ`, with `β(λ)` the
  separating invariant; completing it needs only the standard fact
  that KMS temperatures of the unique tracial ray transform trivially
  under cocycle perturbations — a finite verification against
  Kishimoto--Kumjian's KMS computation, flagged as the cheapest
  possibly-complete solution in this cluster.
