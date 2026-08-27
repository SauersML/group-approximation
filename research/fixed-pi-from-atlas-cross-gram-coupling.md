---
rg: 2
id: fixed-pi-from-atlas-cross-gram-coupling
kind: route
title: Apply the positive-mass PI inequality to the full Atlas overlap coupling
target: fixed-pi-degree-fingerprints-packet-label-factor
requires:
  - pauli-overlap-yields-positive-spectral-corner
  - positive-mass-four-pauli-intertwiner-forces-pi-gap
  - atlas-kernel-relators-couple-cross-gram-to-four-pauli
---

The overlap gives `||T||_2^2>=5/64-o(1)`, while `(AKC2)` and `(AKC3)` make
the right side of `(PMI1)` tend to zero.  The left side tends to at least
`sqrt(5)`.  This contradiction supplies the fixed degree-two PI fingerprint
on canonical regular-Atlas microstates and hence the terminal PI route.
