---
rg: 2
id: sl3-central-dual-via-letter-multiplicity-stinespring
kind: route
title: Convert the central separator to a lattice actor using only the stable-letter multiplicity blocks
target: sl3-hnn-central-dual-gap-vanishes
requires:
  - central-letter-averages-matrix-range-separators
  - hnn-matrix-range-obstruction-is-a-letter-multiplicity-coupling
  - hnn-stable-letter-rounds-to-finite-order
---

**INVALIDATED PROPOSAL.**  Round the stable letter to finite order, split
its commutant into spectral multiplicity blocks, interpret the bounded
separator on each block through the Choi cone, and use the block
Stinespring representations as a genuine lattice actor.  Then apply the
Kazhdan argument to force the separator gap to vanish.

`letter-central-matrix-range-separation-is-morita-neutral` proves that this
conversion has no content: the support function and the separator gap split
exactly over those blocks, and arbitrary positive gaps can be amplified
under an asymptotically Haar central letter with unchanged off-spectral
multiplicity mass.  A Stinespring actor exists on a block only after a ucp
comparison on that same block has already been supplied, which is precisely
the desired matrix-range conclusion.

The full arithmetic HNN selection is not used by this proposal.  A viable
replacement must couple the `T`-multiplicity blocks to the conjugate-letter
blocks for `phi(h)Tphi(h)^*`, or otherwise use a relation involving
`h=diag(p,1,p^(-1))`; one-letter multiplicity structure cannot close the
gap.

