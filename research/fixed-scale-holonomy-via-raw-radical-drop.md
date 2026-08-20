---
rg: 2
id: fixed-scale-holonomy-via-raw-radical-drop
kind: route
title: Replace the nonlinear Schur child center by fixed forbidden radical words
target: fixed-scale-contextual-multiplicity-holonomy
requires:
  - boolean-violation-is-one-raw-radical-qubit-drop
  - groupify-raw-radical-violation-chart
  - non-ce-bcs-has-robust-approximate-energy-gap
  - finite-schur-clifford-packet-flexible-hs-exactification
  - bounded-overlap-syndrome-energy-accounting
  - contractive-computation-ladder
---

Compile each forbidden context atom by its literal-cycle block.  Satisfying
mass occupies a `2^N` simple, while forbidden mass splits among four
raw-word-labeled `2^(N-1)` simples.  The radical chart transports those four
branches at the common half-spin scale and resets the selectors.  Total
forbidden Hilbert mass therefore contributes twice the returned copy count.
The robust BCS gap forces a positive density of such events, and the
contractive ladder absorbs the polynomial chart and word-derivation losses.
