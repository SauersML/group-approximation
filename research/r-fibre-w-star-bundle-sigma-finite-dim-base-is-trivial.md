---
rg: 2
id: r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial
kind: claim
title: A hyperfinite W*-bundle over a countable union of finite-dimensional compacta is trivial
distinct_from:
  r-fibre-w-star-bundle-finite-dim-base-is-trivial: that is Ozawa's Corollary 16 for bases of finite covering dimension; this allows every compact metrizable countable union of closed finite-dimensional subsets, such as the one-point compactification of the disjoint union of all cubes, and localizes non-triviality to the stable kernel of the infinite-dimensional derived sequence.
  bauer-gamma-failure-localizes-to-infinite-dim-point: that confines non-local-triviality to points with no finite-dimensional neighbourhood; this confines it to the smaller kernel K^(∞) where the derived sequence of such points stabilizes, and makes every countable-dimensional base admissible.
  r-fibre-w-star-bundle-locally-trivial-is-trivial: that assumes local triviality everywhere; this proves triviality from a dimension condition on the base with no local-triviality hypothesis.
  lin-condition-c-boundary-strict-comparison-z-stable: that proves Z-stability from strict comparison for algebras whose tracial boundary satisfies Lin's condition (C); this is a theorem about abstract W*-bundles, needs no C*-algebra and no comparison hypothesis, and on Bauer simplices yields uniform property Gamma.
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks for a nontrivial bundle over some base; this rules out every countable-dimensional base for such a witness.
artifacts:
  - research/artifacts/w-bundle-sigma-finite-dim-triviality-2026-09-12.md
---

Let `M` be a strictly separable continuous W*-bundle over a compact metrizable
space `K` with every fibre isomorphic to `R`.

**Derived sequence.**
- `X_inf` is the set of points of `X` with no closed neighbourhood of finite covering dimension.
- `K^(0) = K`, `K^(δ+1) = (K^(δ))_inf`, and at limit ordinals take intersections.
- `K^(∞)` is the set where the sequence stabilizes.

**Theorem.**
1. If `K` is a countable union of closed finite-dimensional subsets, equivalently if `K^(δ) = ∅` for some `δ`, then `M ≅ C_σ(K,R)`.
2. For every such `M`, the non-local-triviality locus satisfies `Z(M) ⊆ K^(∞)`.

**Examples of admissible bases:**
- the one-point compactification of `⊔_n [0,1]^n`;
- wedges of cubes shrinking to a point;
- every countable-dimensional compactum.

The Hilbert cube is not admissible.

**What this rules out.**
- The one-point compactification of the cubes, recorded as the smallest witness shape for BBSTWW Question 3.14, carries no nontrivial bundle.
- A witness base must contain a nonempty closed set whose nonempty relatively open subsets are all infinite-dimensional.

**For algebras.** Let `A` be a unital simple separable nuclear non-elementary
algebra with Bauer trace simplex and `∂_e T(A)` countable-dimensional in this
sense. Then `A` has uniform property Gamma.

**Proof idea.**
- Lift exact central matrix units from a trivial restriction to an open neighbourhood.
- Patch two such systems with the flip unitary `exp(iπ g h)`, at a cost independent of dimension.
- Induct on the length of the derived sequence, and conclude with Ozawa's Theorem 15 (ii).
