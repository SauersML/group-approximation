---
rg: 2
id: common-hecke-character-orbit-saturation-closes-oci4
kind: route
title: Saturate the Hecke character source under both order-seven heads
target: finite-coordinate-el20-active-cut-inherits-order-seven-anchor
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - middle-index-order-seven-orbit-cut-is-native-scale-neutral
---

Starting with the exactified common Hecke source `Q_n`, intersect its
translates under a fixed word ball in the two order-seven heads.  The hoped
for repair of the one-step leakage argument is to retain a positive
orbit-saturated subcut `E_n<=Q_n` on which every boundary term needed for
both seventh-power telescopes tends to zero.  The two odd anchors would then
remove both reservoir involutions on one source.

This route is refuted by
`el20-order-seven-heads-force-zero-common-hecke-reducing-cut`.  In the
ultraproduct, such a positive saturated cut would give a nonzero
`E<=Q` reducing both heads, while the exact seven-corner commutator identity
forces every such projection to be zero.
