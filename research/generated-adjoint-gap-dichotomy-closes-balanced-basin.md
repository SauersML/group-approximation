---
rg: 2
id: generated-adjoint-gap-dichotomy-closes-balanced-basin
kind: route
title: Quarantine raw outliers and split the diffuse block by its generated-adjoint gap
target: complete-pair-overlay-uniform-hs-basin-capture
requires:
  - balanced-overlay-common-reducing-outlier-cut
  - fixed-parity-faces-exactify-with-loewner-row-square-control
  - pair-sum-faces-control-shared-commutator-energy
  - row-square-equality-variance-transfers-averaged-pinching-gap
  - uniform-generated-adjoint-gap-rounds-to-central-code
  - balanced-overlay-gapless-adjoint-sector-rounding
---

The common raw-square-function cut removes the high-operator-norm sector at
vanishing trace and movement cost.  On its complement, exactify the bounded
faces with the established Loewner row-square ledger, take weighted cloud
averages and signs, and use pair-sum congestion to transfer the balanced
energy to parity and complete-pair energy of one shared reflection tuple.

Decompose the retained tuple according to the generated-adjoint dichotomy.
Every block with Poincare constant bounded below is rounded directly, in the
same algebra, to central commuting code reflections by
`uniform-generated-adjoint-gap-rounds-to-central-code`.  The remaining
gapless blocks are rounded or split at summable cost by
`balanced-overlay-gapless-adjoint-sector-rounding`.  Reconstruct each
bounded face PVM from the final shared coordinate reflections and fill the
quarantined block with scalar code characters.  The total correction tends
to zero and enters the fixed mixed-norm Newton tube, proving basin capture.

