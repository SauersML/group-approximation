---
rg: 2
id: slow-length-frequency-bs-hull-proof
kind: route
title: Diagonalize return phases, count the low-frequency band, and choose both cutoffs slowly
target: regular-short-low-frequency-bs-source-hull-is-sublinear
requires:
  - long-bs-packet-source-mass-is-frequency-small
  - bs14-regular-character-forces-sublinear-fixed-source
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Use the scalar packet decomposition to prove `(SLH6)`.  Haar convergence of
the `R_n` spectral laws permits a slow shrinking band satisfying `(SLH7)`.
Choose the length cutoff still more slowly so its product with the band
rank density vanishes.  Chebyshev's inequality pays the source outside the
band, and the long-source theorem pays the source outside the length
cutoff.  Both exits are fixed BS words applied to the retained source, so
they lie in the same invariant hull.
