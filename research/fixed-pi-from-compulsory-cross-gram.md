---
rg: 2
id: fixed-pi-from-compulsory-cross-gram
kind: route
title: Feed the compulsory positive overlap into the four-Pauli PI inequality
target: fixed-pi-degree-fingerprints-packet-label-factor
requires:
  - pauli-overlap-yields-positive-spectral-corner
  - positive-mass-four-pauli-intertwiner-forces-pi-gap
  - compulsory-pauli-cross-gram-is-four-word-intertwiner
---

Choose the heavier ordered cross-Gram contraction.  The overlap theorem and
`(PCG1)` give `||T||_2^2>=5/64-o(1)`.  The common-word claim gives `(PCG2)`
and `(PCG3)`.  Apply `(PMI1)` with `beta=5/64`; its right side tends to zero
while its left side tends to

```text
8 sqrt(5/64)=sqrt(5)>0.
```

This supplies the fixed degree-two PI contradiction.  No scalar spectator
gap, mutual bicommutant theorem, spectral cutoff, or near-full cross-Gram
moment is used.
