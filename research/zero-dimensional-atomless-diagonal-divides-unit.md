---
rg: 2
id: zero-dimensional-atomless-diagonal-divides-unit
kind: claim
title: A strict-comparison algebra on a Bauer simplex with a zero-dimensional diagonal carrying atomless extreme traces divides its unit
distinct_from:
  bauer-c-space-strict-comparison-divides-unit: that divides the unit under a covering hypothesis on the tracial boundary; this imposes nothing on the boundary and asks instead for a zero-dimensional commutative subalgebra on which extreme traces are atomless.
  bauer-strict-comparison-unit-divides-iff-atomless-element: that is the general criterion by one element with small atoms; this is its special case where an injective function on a zero-dimensional diagonal supplies the element.
artifacts:
  - research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md
---

Let `A` be unital, simple, separable, exact and non-elementary, with strict
comparison and a nonempty Bauer trace simplex with extreme boundary `K`. Suppose `A`
contains a unital commutative C*-subalgebra `C(Y)`, with `Y` compact metrizable and
zero-dimensional, such that every `λ ∈ K` restricts to an atomless probability measure
on `Y`. Then the unit of `A` is tracially `N`-divisible for every `N`.
- So `A` is pure (`bauer-strict-comparison-pure-iff-divisible-unit`).
- If `A` is also nuclear with tracially locally finite nuclear dimension, `A ≅ A ⊗ Z`
  (`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`).

No covering hypothesis on `K` is used, so this covers Hilbert cube boundaries.

**Example, not checked against the literature.** Reduced twisted groupoid algebras of
minimal principal étale groupoids with Cantor unit space, with their Cartan subalgebra
`C(G^0)`. Traces restrict to invariant measures, and infinite orbits make them
atomless. No novelty is asserted for this example; dynamical-comparison routes may
already cover it.

**Proof** (route `zero-dimensional-atomless-diagonal-divides-unit-proof`). An injective
continuous `h: Y → [0,1]` exists because `Y` embeds in the Cantor set. Its spectral
distribution at `λ` is the pushforward of `λ|_{C(Y)}`, which is atomless. So (ii) of
`bauer-strict-comparison-unit-divides-iff-atomless-element` holds for every `ε`.

**Model test.**
- The hypothesis fails for `C(K)`: the diagonal `C(K)` carries the point traces, which
  are atoms.
- A UHF algebra satisfies it with its Cantor diagonal: the unique trace restricts to the
  product measure, which is atomless.

Unreviewed.
