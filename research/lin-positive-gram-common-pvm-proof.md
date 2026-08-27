---
rg: 2
id: lin-positive-gram-common-pvm-proof
kind: route
title: Apply Lin's spectral PVM rounding to the normalized Gram state
target: positive-cross-gram-state-rounds-to-common-pvm
requires:
  - lin-near-synchrony-selects-one-state-corner
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - labelled-pvm-branch-gram-gives-lin-corner
artifacts:
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
---

Write `G=sigma U`, put `s=sigma/sqrt(m)`, and conjugate the second packet by
the polar unitary. The resulting standard-form strategy is exactly
`delta=E/(2m)` synchronous. Lin's symmetrization and Proposition A.8 give
PVMs on the spectral cuts of the Gram density. A cut in the fixed interval
corresponding to `[1/4,1/2]` has trace at least `m/2`; averaging the movement
bound selects one such cut with squared error `O(delta^(1/4))`. The lower
spectral bound on that cut transfers the estimate to the polar-gauged second
packet. Orthogonality proves the final labelled-block identity directly.
