---
rg: 2
id: radu-bmw-lattice-nonsofic
kind: claim
title: Radu's non-residually-finite BMW lattice is not sofic
distinct_from:
  radu-bmw-lattice-sofic: this is its negation.
  titz-witzel-kernel-nonsofic: that is nonsoficity of the simple Kazhdan building lattice; this is nonsoficity of its product-of-trees subgroup, which implies that claim.
  openai-leavitt-unit-nonsofic: that is nonsofic through property (T) and one-sided compression; this lattice has the Haagerup property, so any proof must use a different mechanism.
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

**OPEN.**  This is the negation of `radu-bmw-lattice-sofic`.  If established,
it makes the smallest Titz--Witzel kernel nonsofic
(`titz-witzel-kernel-nonsofic-from-radu-lattice`).  It would also give a nonsofic lattice in a product of trees, hence a
nonsofic group with the Haagerup property. It gives `F_2 × F_2` a free nonsofic action
(`f2xf2-nonsofic-action-from-radu-lattice-nonsofic`), but never a mixing one through an
induced action: the vertical closure is locally `C_2`, and the horizontal kernel is an
infinite normal subgroup of the envelope (`radu-lattice-induced-actions-are-never-mixing`).
A mixing witness would also need `radu-bmw-lattice-embeds-in-infinitely-transitive-tree-lattice`.

## Attempts

* **Robust Radu argument.**  `radu-bmw-lattice-nonsofic-via-commutator-collapse`
  reduces this claim to `radu-commutator-collapse`: the commutator
  `[y(xz)^2y, xz]` vanishes asymptotically along every approximate solution.
  Every other step of the non-residual-finiteness proof is already
  quantitative.  The published exact input is [Rad20, Proposition 5.4] (via
  Titz Mite--Witzel Proposition 3.4(3)--(4)).  It is a profinite-closure
  statement, and whether its proof survives sparse defects is unread.
* **What a proof would produce (ex-tree-lattice-mixing, 2026-09-13; unreviewed).**
  - `Gamma_R` is a marked limit of `Gamma_R/gamma_k(Lambda_v)`, extensions of free nilpotent groups
    by a cocompact arithmetic lattice in `PGL_2(Q_2)^2`
    (`radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`).
  - So nonsoficity of `Gamma_R` would make one of them a nonsofic amenable-by-residually-finite
    group, refuting amenable-by-sofic permanence (open even for finite cyclic kernels).
  - Radu's published mechanism (arXiv:1712.01091v1 Prop. 5.1, pp. 41–42, read for `Gamma_(4,4)`)
    picks elements of `ker φ` fixing a ball and moving a neighbour. Almost actions have no such
    kernel elements, so a different finite-structure input is needed.
  - The linear quotient supplies explicit congruence models and super-strong approximation
    (`radu-horizontal-quotient-is-arithmetic-lattice`).
