---
rg: 2
id: titz-witzel-kernel-sofic
kind: claim
title: The smallest Titz--Witzel simple Kazhdan kernel is sofic
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
distinct_from:
  titz-witzel-soficity-is-one-finite-csp: that is the established equivalence between soficity of this kernel and a marked three-permutation gate; this is the open soficity assertion itself.
  titz-witzel-exact-kazhdan-mf-radical-over-z: that proves every clause of the torsion-free exact-radical target except soficity; this is the one missing clause, for the smallest kernel.
---

**OPEN.**  Let `K = Gamma_1^2` be the smallest Titz Mite--Witzel lattice
(arXiv:2509.05054v2, Theorem 4.1; the index-two subgroup of the 15-generator
group of their Proposition 4.3).  It is finitely presented, torsion-free,
infinite, simple and Kazhdan.  The claim is that `K` is sofic.

Equivalent finite forms are `titz-witzel-soficity-is-one-finite-csp`,
`titz-witzel-sofic-gate-two-generators-four-approximate-relators` and
`titz-witzel-two-generator-involution-sandwich-normal-form`.

Value.  `K x Z` then closes `torsion-free-sofic-exact-mf-radical-over-z`
through `torsion-free-sofic-exact-mf-radical-via-titz-witzel`.  `K` would be
a finitely presented sofic Kazhdan group that is not residually finite
(Alekseev--Thom Open Problem 6.1).  Since `K` is isolated and not elementary
sofic, it would also answer Cornulier's Question 5 positively.

## Attempts

* **Elementary permanence.**  Dead: `titz-witzel-kernel-not-elementary-sofic`.
  No finite chain of subgroups, direct limits, marked limits and amenable
  extensions reaches `K`, and `K` is not a nontrivial marked limit.
* **Structured finite models.**  The cyclic affine, cyclic normalizer,
  central-square-lift and regular-packet ansatzes, a trivial second
  matching, and sparse surgery on exact sheets were each proved to collapse
  the mark or to keep a linear defect (the `titz-witzel-*` ansatz nodes).
* **Through the Radu sublattice.**  Soficity of `K` forces soficity of
  Radu's non-residually-finite BMW lattice, `radu-bmw-lattice-sofic`.  Its
  marked gate must keep `[y(xz)^2y, xz]` macroscopically nontrivial and must
  not factor through the horizontal tree quotient (artifact Sections 3--4).
