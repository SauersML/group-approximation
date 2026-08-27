---
rg: 2
id: nonhyperlinear-from-coherent-heisenberg-module-decoder
kind: route
title: Decode one surviving root into a positive-density Leavitt module
target: non-hyperlinear-group
requires:
  - coherent-heisenberg-multiplicity-decoder
  - hs-finite-heisenberg-windows-have-compatible-density-measures
  - approximate-relative-leavitt-cell-kills-active-trace
---

In a faithful hyperlinear model, a surviving characteristic-two root gives a
nonzero spectral projection `(1-u)/2`; faithfulness of the ultraproduct trace
makes its trace positive.  The coherent decoder promotes the compatible
finite additive and Heisenberg multiplicities on that active sector to one
positive-density approximate binary Leavitt module.

The finite-matrix Leavitt trace inequality forces the trace of this module
corner to be bounded by the sum of its relation defects, which tend to zero.
This contradicts positive density.  Normal generation of the chosen root
then rules out a faithful hyperlinear model of the whole group.
