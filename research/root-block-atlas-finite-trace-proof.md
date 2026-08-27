---
rg: 2
id: root-block-atlas-finite-trace-proof
kind: route
title: Pull back a normalized finite-dimensional corner trace
target: root-block-piecewise-transport-cannot-host-nonce-bcs
requires:
  - bcs-corner-model-is-a-compatible-projection-atlas
---

The finite-dimensional star algebra `qC[K]q` has a faithful unital
representation in some matrix algebra: use the restriction of the left
regular representation to `q l2(K)`.  Its normalized matrix trace is positive,
unital, tracial, and Connes embeddable.  Pulling this trace back through the
map supplied by `(BPA1)--(BPA3)` gives a Connes-embeddable tracial state on
`A(B)`, contrary to the hypothesis.  This argument does not require the
atlas map to be injective.
