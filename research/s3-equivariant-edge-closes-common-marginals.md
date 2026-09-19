---
rg: 2
id: s3-equivariant-edge-closes-common-marginals
kind: route
title: Use one S3-equivariant stable word to eliminate independent endpoint rotations
target: three-chart-affine-clifford-return-incidence
requires:
  - s3-equivariant-affine-clifford-return-edge
  - finite-symmetry-equivariant-edge-has-one-holonomy
  - affine-selector-clifford-rank-swap-balanced
  - rank-one-no-signaling-pairing-floor
---

The concrete edge claim supplies one `S_3`-equivariant semidirect edge whose
three directional restrictions are the radical comparisons.  The general
equivariant-edge theorem makes all three transports conjugates of one stable
word, so a single multiplicity unitary occurs on their merged spin carrier.
Because the source and endpoint events are conjugated together, their scalar
marginals obey `(RNS1)` up to the fixed `O(sqrt(E))` packet loss.  The
rank-one no-signaling floor then gives `(TCR1)` and closes the common-marginal
incidence without identifying old selectors across contexts.
