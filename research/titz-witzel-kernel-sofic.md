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
refuted_by:
  - titz-witzel-kernel-nonsofic
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
* **Biography of a minimal counterexample: partial-action rounding (swarm-0917, inverter).** The
  one-sentence reason every cut-and-paste construction fails is ESTABLISHED in
  `kazhdan-consistent-partial-models-round-to-finite-actions`. Suppose a permutation tuple has
  consistent monodromy on a set of density `1 - eta`, meaning that every trivial word read inside
  the set closes. Globalizing the partial action and projecting with property (T) forces every
  generator to move at most `(2 + 2/kappa^2) eta n` points. This kills every model that agrees
  with a genuine `K`-set (finite, a coset space, the building, a boundary) on all but `eta n`
  points and is re-glued arbitrarily elsewhere. The invariant is the partial action on the
  agreement set, and the dying step is its globalization. A sofic model of `K` therefore has
  three forced properties.
  * (i) Its consistency deficit is at least `c_kappa` times its mark (so it is not a sparse
    re-gluing of any `K`-set).
  * (ii) Its open trivial words sit far from every relator defect, at filling radius
    `>~ log(c_kappa m/eps)/log(2|S|)` (`kazhdan-sofic-models-carry-long-scale-monodromy`), so
    fixing relators on balls (Kun, Alekseev--Drigalla, radius-`r` rigidity) supplies no mark.
  * (iii) Its commutant is non-ergodic (`kazhdan-ergodic-sofic-centralizer-forces-lef`).

  The negative direction reduces to the purely combinatorial deletion-repair statement of
  `titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair`: nonsoficity holds iff every almost
  solution becomes consistent after deleting `o(n)` points. Where this approach dies: neither
  direction of (P2) is proved. A positive answer needs a model with logarithmic-scale monodromy
  that is not confined to `o(n)` points, and no construction of such a model for `K` is known.
  The unexplored recipes are non-normal (non-Galois) finite branched covers of the quotient
  complex, with inhomogeneous branching data. Galois branched covers have the same local group at
  every lift of a branch point. That suggests a linear defect, but this was checked only
  heuristically and is not recorded as a claim.
