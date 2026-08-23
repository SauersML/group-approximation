---
rg: 2
id: rstar-core-affine-cover-proof
kind: route
title: Label the kernel caps and reconstruct fixed cap rows outside it
target: rstar-core-character-profiles-induce-an-exact-affine-cover
requires:
  - rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel
  - rstar-cap-support-is-one-character-row
---

Fix `beta`.  The core rows have odd parity plus their chosen nonzero tail
character.  Reverse peeling retains at most two assigned coordinates in
each remaining row; choose an unused tail coordinate `j` and impose `x_j=1`
as in the two-retained-coordinate section.  All resulting equations are
affine, so their solution set and its visible projection `A_beta` are
affine.  Every row solution lies in `R_*`, proving `A_beta subseteq C`.

Conversely, take any `phi in C` and any target witness.  Every tuple on a
core row lies in at least one maximal Fano cap.  Choose such a character for
each core row, producing a profile `beta`.  Reverse peeling changes only
nonvisible, nonkernel variables and preserves `phi`, so it produces a
solution of the full affine branch.  Hence `phi in A_beta` and the union in
`(RAC2)` is all of `C`.

If `S subseteq A_beta`, choose one affine-branch witness above each member of
`S`; their range at every row lies in that row's fixed maximal cap.  This is
a deterministic cap-valued witness section.  Conversely, any cap-valued
section has one character per row by the second prerequisite.  Restrict its
profile to the core and reconstruct the peeled rows; its visible support is
therefore contained in the associated `A_beta`.  This proves `(RAC3)`.

