---
rg: 2
id: kt-component-family-from-expander-decomposition
kind: claim
title: An expander decomposition yields a component family with exact directed expansion and negligible uncovered mass
distinct_from:
  kt-good-components-markov-selection: that selects good full expander components and proves uniform bounds for their completed labels, without the expands field; this prunes the good components by a maximal sparse cut, proves exact directed expansion there, and assembles the whole ComponentFamily value together with its uncovered mass.
  retained-sets-keep-component-family-uniform-fields: that transfers size, multiplicativity and injectivity from full models to arbitrary retained subsets; this chooses the retained sets, proves the expands field on them, and builds the family from an expander decomposition and an enumeration.
artifacts:
  - GroupApproximation/KunThom/SequentialComponentFamilyPruning.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyCompletion.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyLevels.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyObjects.lean
  - GroupApproximation/KunThom/SequentialComponentFamily.lean
---

**ESTABLISHED, proved here.** Blueprint steps 1–2 of Kun–Thom Theorem 4.1
(`research/artifacts/kt-theorem-4-1-blueprint-2026-09-12.md`), lane
kt41-seq-decomp. Namespace `GroupApproximation.SequentialComponentFamily`.

**Setting.**
- `S` is a sofic approximation of an infinite group `K`.
- `T` is a finite symmetric generating set.
- `D : ExpanderDecomposition S T`, with Cheeger constant `h`.
- `enum : ℕ → K` is surjective.

**Statement.** `componentFamily D hsymm hgen hT enum henum` is a
`CentralizerNormalizationImprove.ComponentFamily K T` with Cheeger constant
`h / (8 |T|)`.
- Objects at index `n`: the components that are good at a diagonal level.
- Model of an object: the component minus one maximal sparse cut of its
  completed generator labels.
- Labels: the completed labels, completed again on the model.

The uncovered mass, meaning components that are not objects plus pruned
points of objects, is `o(|S_n|)` (`uncoveredMass_negligible`). Object sizes
plus uncovered mass equal `|S_n|` (`sum_card_objectModel_add_uncoveredMass`).

**Why pruning is needed.** `ComponentFamily.expands` asks for an exact
directed Cheeger bound on every subset of every object. Completed component
labels expand only above a scale: a set smaller than the local edit budget can
be fixed by every label.

DERIVATION
kt-component-family-from-expander-decomposition-proof
