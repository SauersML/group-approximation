---
rg: 2
id: kt-good-components-markov-selection-proof
kind: route
title: Diagonal Markov selection over six per-component error families
target: kt-good-components-markov-selection
requires: []
artifacts:
  - GroupApproximation/KunThom/CentralizerNormalizationUniformMarkov.lean
  - GroupApproximation/KunThom/CentralizerNormalizationUniformGood.lean
---

Lean: `GroupApproximation.CentralizerNormalizationUniform.exists_goodComponents`,
landed in a3ae7dd4c with root imports, probe
`kt41-g1-uniform.green.0912-132348-25521`, axiom closures
`[propext, Classical.choice, Quot.sound]`.

The six error families and the landed estimates giving their negligible
totals:

* completed product errors: `componentMultiplicationError_sum_negligible`;
* ambient collisions of two distinct elements inside a component:
  `SoficApproximation.collisionError_negligible` with
  `BlockIndex.sum_card_filter`;
* exits of a fixed element: `all_almost_invariant` with
  `sum_componentGeneratorExits`;
* small components: `smallBlockVertices_negligible` with
  `sum_smallBlock_card`;
* components that are not cluster good: `badClusterComponentMass_negligible`;
* local edit budgets: `componentLabelEditBudget_sum_negligible`.

`exists_isGood` enumerates the error kinds, takes the `diagonalLevel` `J n`
of the accumulated normalized errors, and bounds the bad mass by `J n + 1`
times the totals of the first `J n + 1` error counts (Markov plus a union
bound).  Label injectivity on `T` follows from collisions and exits below
`|C| / 4` each, since equal completed labels force an ambient collision at
every point whose two images stay inside the component.
