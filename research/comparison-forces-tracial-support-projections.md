---
rg: 2
id: comparison-forces-tracial-support-projections
kind: claim
title: Projection comparison in the tracial ultrapower forces tracial support projections for nuclear algebras with tracially locally finite nuclear dimension and bounded rank density
distinct_from:
  tracial-projection-comparison-forces-uniform-gamma: that is the universal assertion "comparison forces uniform Gamma" for all nuclear algebras; this is equivalent to its restriction to algebras with tracially locally finite nuclear dimension and bounded rank density, restated as a single-element existence property with no centrality.
  uniform-gamma-iff-tracial-support-projections-and-division: that proves uniform Gamma equivalent to support projections plus division under the dimension hypothesis; this asks whether comparison of existing projections already supplies the support projections.
  gamma-failure-invisible-to-projection-comparison: that asks for an algebra with comparison and without uniform Gamma, with no locus restriction; this is the positive assertion on one locus, where such an algebra is exactly one with comparison and a positive support gap.
artifacts:
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with `T(A) ≠ ∅`. Suppose `A` has these three properties:
- tracially locally finite nuclear dimension;
- bounded rank density (RD_b, as in `ultrapower-comparison-with-rank-density-divides-projections`);
- projection comparison by limit traces in every `M_k(A^U)`.

Then `γ_A(a) = 0` for every `k` and every positive contraction `a ∈ M_k(A)`. That
is, every such `a` has near projections `b ∈ closure(a M_k(A) a)` with uniformly
small defect `τ(b − b²)` and `τ(b) ≥ τ(a) − ε` for all traces.

**Why it matters.**
- By `uniform-gamma-iff-tracial-support-projections-and-division` and
  `ultrapower-comparison-with-rank-density-divides-projections`, this claim is
  equivalent to `tracial-comparison-gives-gamma-on-lfnd-rank-density-locus`.
- Every unital Toms--Winter counterexample on this locus would refute it, by
  `strict-comparison-compares-ultrapower-projections`.
  - Such a counterexample cannot have norm locally finite nuclear dimension,
    since `rank-density-and-strict-comparison-give-purity` and Winter's theorem
    already give Z-stability there. Only tracially-but-not-norm locally finite
    algebras are left.
  - What stays open on the whole locus is the weaker hypothesis: comparison of
    ultrapower projections without strict comparison of the algebra.

## Attempts

- **Moving rank-density projections under `a`.** Comparison moves projections
  under projections, and `a` is not a projection.
  - The dilation projection of `a` in `M_{2k}(A)` is equivalent to `1_k ⊕ 0` in
    every algebra, through `[[a^{1/2}, (1−a)^{1/2}], [0, 0]]`.
  - So comparing it carries no information about projections under `a`.
- **Spectral cutoffs.** A steep function of `a` is a near projection only where
  the spectral distributions of `a` put uniformly small mass near the cutoff.
  - Take `a` from a finite stage of an AH or doubling system. Branch traces
    concentrate on single points of that stage, so its distributions have atoms
    of fixed mass at every level the stage eigenvalues sweep.
  - No uniform cutoff exists. Splitting those atoms is the claim itself.
- **A commuting diffuse element.** Theorem 1(a) of the artifact cuts support
  projections from any unital `M_N ⊂ M_k(A^U)` commuting with `a`.
  - Division of projections (from comparison and RD_b) supplies unital
    `M_{2^j}` in `M_k(A^U)`, but none commuting with `a`.
  - Conjugating one into `{a}'` is single-element McDuff, which on this locus
    is equivalent to uniform Gamma, so this is circular.
- **Real rank zero.** Real rank zero of `A^U` gives the claim's conclusion
  through approximate units of projections in `closure(aA^Ua)`. Deriving it from
  comparison is the converse of CCEGSTW Proposition 7.2, recorded as unknown on
  `tracial-projection-comparison-forces-uniform-gamma`.
- **Bauer boundary (heuristic, not proved).** The conclusion is a 2-norm
  continuous selection, over the extreme boundary, of subprojections of the
  support of `a` with trace at least `τ(a)`.
  - Locally trivial pieces admit it, by the partition-of-unity construction of
    `trivial-r-fibre-bundles-compare-equal-trace-projections` carried out inside
    `{a}'`.
  - Failure should sit where non-triviality localizes
    (`bauer-gamma-failure-localizes-to-infinite-dim-point`).
