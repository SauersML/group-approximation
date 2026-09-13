---
rg: 2
id: bauer-strict-comparison-unit-divides-iff-atomless-element
kind: claim
title: On a Bauer simplex with strict comparison, the unit divides iff some self-adjoint element has no heavy eigenvalue at any extreme trace
distinct_from:
  bauer-unit-division-defect-uniform-criterion: that characterizes division by summable covers with local order zero maps; this characterizes it by one self-adjoint element with uniformly small atoms, with no covers and no matrix units.
  comparison-forces-tracial-support-projections: that asks for support projections under positive elements and uses spectral cutoffs of a given element; this asks only for existence of one element with small atoms, and uses a central CDF transform to make its distributions uniformly Lebesgue.
  ultrapower-comparison-with-rank-density-divides-projections: that divides projections from rank density of every profile; this needs only one diffuse element, from which constant-trace projections follow on a Bauer simplex.
artifacts:
  - research/artifacts/ex2-tw-atomless-element-division-2026-09-13.md
---

**Setting.** `A` is unital, simple, separable, exact and non-elementary, with strict
comparison. `T(A)` is a nonempty Bauer simplex with extreme boundary `K`. For self-adjoint
`h` and `λ ∈ K`, `μ_{h,λ}` is the spectral distribution of `π_λ(h)` under `λ`.

**Theorem.** These are equivalent:
- (i) the unit of `A` is tracially `N`-divisible for every `N`;
- (ii) for every `ε > 0` some self-adjoint contraction `h ∈ A` has every atom of every
  `μ_{h,λ}`, `λ ∈ K`, of mass `< ε`;
- (iii) for every `ε > 0` some `u` in the strict closure with `0 ≤ u ≤ 1` has
  `|μ_{u,λ}([0,s]) − s| ≤ ε` for all `λ ∈ K` and `s`.

**Witness form (tracial eigenvalue rigidity).** The unit does not divide iff some
`ε_0 > 0` has the following property. Every self-adjoint `h ∈ A` has an extreme trace `λ`
at which `π_λ(h)` has an eigenprojection of trace at least `ε_0`.

**Proof** (route `bauer-strict-comparison-unit-divides-iff-atomless-element-proof`).
- **(i) ⟹ (ii).** `h = Σ_j (j/N) φ(e_jj)` has atoms at most `max(1/N, defect)`.
- **Small atoms give small concentration.** By compactness of `K`, small atoms give
  uniformly small mass `μ_{h,λ}([x − η, x + η])` for some `η`.
- **Central CDF transform.** `F(λ, s) = ∫ clamp((s − y)/η) dμ_{h,λ}(y)` is jointly
  continuous. `F(λ, h)`, realized in the strict closure through the central `θ(C(K))`, has
  distribution uniformly within `2ε` of Lebesgue.
- **Projections.** Ramps of approximants give projections of constant trace `1/k` in the
  tracial ultrapower. Comparison of ultrapower projections
  (`strict-comparison-compares-ultrapower-projections`) gives a unital `M_k`, and order zero
  lifting gives (i).

**Corollary** (`zero-dimensional-atomless-diagonal-divides-unit`). A unital `C(Y)` in `A`,
with `Y` zero-dimensional and atomless restrictions of all extreme traces, forces the
unit to divide.

**Model test.** In `C(K)`, which is not simple, every self-adjoint has multiplicity-one
eigenvalues at point traces, and no order zero `M_2` is nonzero. A unique-trace algebra
has a diffuse self-adjoint element, and its unit divides.

Unreviewed. It builds on the reviewed ultrapower comparison theorem and on the facts
(F1)–(F5) of `research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md`.
