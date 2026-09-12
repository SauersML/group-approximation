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
nonsofic group with the Haagerup property.

## Attempts

* **Robust Radu argument.**  `radu-bmw-lattice-nonsofic-via-commutator-collapse`
  reduces this claim to `radu-commutator-collapse`: the commutator
  `[y(xz)^2y, xz]` vanishes asymptotically along every approximate solution.
  Every other step of the non-residual-finiteness proof is already
  quantitative.  The published exact input is [Rad20, Proposition 5.4] (via
  Titz Mite--Witzel Proposition 3.4(3)--(4)).  It is a profinite-closure
  statement, and whether its proof survives sparse defects is unread.
