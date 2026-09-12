---
rg: 2
id: kun-expander-decomposition-formalized-proof
kind: route
title: Partition, pack markers, repair the graph, charge the boundary
target: kun-expander-decomposition-formalized
requires: []
artifacts:
  - GroupApproximation/Kun/KunDecomposition.lean
  - GroupApproximation/Kun/KunFinitePartition.lean
  - GroupApproximation/Kun/KunMarkerSelection.lean
  - GroupApproximation/Kun/KunSelectiveRepairExpansion.lean
  - GroupApproximation/Kun/KunBoundary.lean
  - GroupApproximation/Kun/KunUniformRemoval.lean
---

## Direct proof, machine-checked

`exists_expanderDecomposition` assembles five proved layers, and
`propertyT_expanderDecomposition` supplies their hypotheses from property `(T)`
alone.

**The generating set.**  `HasKazhdanPropertyT.exists_identity_pair` gives a
Kazhdan pair `(Q, ε)`; `Group.fg_iff'` gives a finite generating family `F`;
`S = insert 1 (U ∪ U⁻¹)` for `U = Q ∪ F` is symmetric, contains the identity,
generates, and contains the Kazhdan pair -- which is what lets the same set
serve both the spectral input and the graph.

**Partition and neighbourhoods.**  `KunFinitePartition` and
`KunLocalNeighborhood` cut each model into pieces whose local structure is
controlled; `exists_neighborhoodMultiplicity` bounds how often a neighbourhood
can recur.

**Markers and repair.**  `KunMarkerSelection` packs markers into the pieces;
`KunSelectiveRepairGraph` / `KunSelectiveRepairExpansion` rebuild each piece
into a genuinely expanding graph by editing edges only inside it.

**Charging.**  `KunBoundary`, `KunPartitionBoundary` and `KunSmallBoundary`
bound the edits by the boundary of the partition, and `KunUniformRemoval` /
`KunAsymptoticRemoval` push that bound to `o(|Y_n|)` along the approximation,
which is what makes the result a *decomposition of the approximation* rather
than of one model.

Property `(T)` enters once, as the spectral gap that forbids a large sparse
cut; everything after it is finite combinatorics.
