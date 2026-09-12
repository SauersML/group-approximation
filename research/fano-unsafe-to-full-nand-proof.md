---
rg: 2
id: fano-unsafe-to-full-nand-proof
kind: route
title: Choose dual coordinates on a Fano line and compress its three atoms
target: fano-unsafe-support-compresses-to-a-full-nand-packet
requires:
  - rstar-fano-ghost-affine-hull-criterion
  - binary-affine-safe-perfect-support-forces-classical-satisfaction
---

The independent vectors `u,v` extend to a basis of `V`.  Define `alpha` and
`beta` on that basis by the first two rows of `(FUN2)` and extend linearly.
Linearity gives the third row.  The spectral projections of the two parity
observables on the local carrier `E_L` are the sums of the three mutually
orthogonal atoms with the corresponding labels, proving `(FUN3)`.  Positivity
of every atom follows from `L subseteq S` and faithfulness of the supported
trace.
