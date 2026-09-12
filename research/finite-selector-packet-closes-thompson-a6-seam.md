---
rg: 2
id: finite-selector-packet-closes-thompson-a6-seam
kind: route
title: Exactify the fixed S6 selector packet and pin both contextual arms
target: thompson-v-r5-a6-seam-pointwise-synchronization
requires:
  - bleak-quick-adjacent-seam-retains-finite-selector-packet
  - finite-s6-selector-centralizer-pins-common-pivot-arm
  - gowers-hatami-finite-group-hs-stability
---

Apply finite-group HS stability to the map `Phi` from the selector-packet
claim.  Since `S_6` is fixed, the flexible exactification and its discarded
corner cost are `O(delta)` after changing one universal constant.  On the
exact representation, `(FSC3)` bounds the distance of each arm from the
distinguished common-pivot arm by its three selector commutators.  Pulling
the estimate back to the original compression and using `(BSP1)` gives

```text
||S-S'||_2 <= C delta.                                           (FSP1)
```

The common R2 pivot relation transports the same estimate to the other arm.
Telescope the two arm products approximating the contextual Carmichael
cycles to obtain `(A6S2)`.  The chart part of the finite packet retains
`(A6S1)`, proving the pointwise seam claim with constants independent of
dimension and packet size.

