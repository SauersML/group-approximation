---
rg: 2
id: fpbs-finite-normal-quotient-lifts-price-one
kind: claim
title: If the quotient of a countable group by a finite normal subgroup has fixed price one, the group has fixed price one
distinct_from:
  fpbs-finite-fiber-cost-bound: that compares two free actions of one group across a factor map with finite fibers; this compares a free action of a group with an action of its quotient by a finite normal subgroup on a fundamental domain, so the acting groups differ.
  bernoulli-lifts-across-finite-kernels-force-virtual-splitting: that asks when a free action of the quotient lifts to the extension; this starts from an arbitrary free action of the extension, so no lifting is needed.
  fpbs-wq-normal-price-one-subgroup-forces-price-one: that lifts fixed price one from an infinite wq-normal subgroup; this lifts it from a quotient by a finite normal subgroup, which is not a subgroup.
artifacts:
  - research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md
---

**Statement.** Let `F` be a finite normal subgroup of a countable group
`Gamma`. If `Gamma/F` has fixed price one, then `Gamma` has fixed price one.

**Quantitative form.** For every free p.m.p. action of `Gamma` on `(X, mu)`,
`Gamma/F` acts freely, preserving the normalized measure, on a Borel
fundamental domain `D` of the `F`-action. The orbit relation is `R_Gamma|D`,
and

    C(R_Gamma) - 1 = (C(R_(Gamma/F) on D) - 1) / |F|.

**Scope.** The converse direction, from `Gamma` to `Gamma/F`, is not asserted.
It would need every free action of `Gamma/F` to arise on a fundamental domain,
that is, to lift across the finite kernel.
