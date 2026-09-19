---
rg: 2
id: kun-expander-decomposition-formalized
kind: claim
title: Kun's expander decomposition of a sofic approximation, proved in the development
distinct_from:
  hs-expander-block-decomposition: That asks for a normalized-Hilbert-Schmidt analogue of this decomposition and is open; this is the permutation-model statement itself, over the normalized Hamming distance, and is proved.
  kun-thom-expander-centralizer-formalized: That is the second external theorem, which consumes a SINGLE expander on the whole approximation set and concludes LEF; this is the first, which produces a union of expanders and concludes nothing about any group.
artifacts:
  - GroupApproximation/Kun/KunDecomposition.lean
  - GroupApproximation/Kun/KunFixedDecomposition.lean
  - GroupApproximation/Kun/KunPartition.lean
  - GroupApproximation/Kun/KunRepairExpansion.lean
  - GroupApproximation/Kun/KunBoundary.lean
---

ESTABLISHED, and proved here rather than quoted.
`Kun/KunDecomposition.propertyT_expanderDecomposition`: for a finitely
generated infinite group with Kazhdan's property `(T)` and any sofic
approximation `A`, there is a symmetric generating set `S` containing `1` with

    Nonempty (ExpanderDecomposition A S),

i.e. the generator graphs of the approximation become, after editing a
vanishing proportion of edges, a disjoint union of uniformly expanding graphs.
The Kazhdan pair is constructed inside the proof, so the statement carries only
the standard hypotheses.  `Kun/KunFixedDecomposition.expanderDecomposition` is
the same conclusion on a *prescribed* generating set, which is the form the
compression criterion consumes: property `(T)` is transferred to the fixed
generators first.

This is G. Kun, *On sofic approximations of property (T) groups*,
arXiv:1606.04471 (June 2016; the 2019 date some citations carry is a revision
date).  Thirty-two modules stand behind it -- finite partitions, local
neighbourhoods, marker packing, selective graph repair, boundary charging,
rounding and removal -- and none of it is a transcription: the
`LITERATURE_INPUT` roster of `scripts/Audit.lean` is empty.

## Why the number of components is the whole difficulty downstream

The decomposition is a *union* of expanders and the number of parts can grow
without bound -- taking increasingly many disjoint copies of a model preserves
a sofic approximation.  The consumer,
[[kun-thom-expander-centralizer-formalized]], needs one expander on the entire
approximation set.  Bridging that gap is exactly what
[[one-sided-compression-nonsofic-criterion]] does, and it is where the
mathematical content of the nonsofic mechanism sits.

`Kun/KunSpectralCounterexample` records the negative half of the picture: the
naive spectral route to the same conclusion fails.
