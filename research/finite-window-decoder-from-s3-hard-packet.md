---
rg: 2
id: finite-window-decoder-from-s3-hard-packet
kind: route
title: Decode the three Leavitt pairings through the localized S3 hard-cell system
target: finite-window-decoder
requires:
  - regular-chart-wedderburn-coefficient-compiler
  - s3-hard-cell-three-channel-data-is-nondegenerate
  - atlas-hard-packet-s3-channel-decoder
---

Use `regular-chart-wedderburn-coefficient-compiler` to express the exactified
raw `S3` packet and every hard/comb product as finite multiplicity-corner path
sums.  The established three-channel data fixes the carrier Clebsch--Gordan
coefficients; `atlas-hard-packet-s3-channel-decoder` supplies the missing
full-rank relation system and solves it for the three common-coordinate
defects `(S3D2)`.

Those are exactly the reduced inputs of `finite-window-decoder`.
`TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md` turns the two
diagonal defects into spectral invariance for `L0,L1`; the crossed defect then
survives on the same positive-density spectral cut.
`leavitt-multiplicative-trace-floor` supplies the dimension-free terminal
contradiction.  No reconstruction of an arbitrary common coefficient algebra
and no four-arrow synchronization theorem is inserted between the channel
rank gate and the existing endpoint.
