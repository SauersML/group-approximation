---
rg: 2
id: atlas-a4-gl5-dual-packet-collision-screen-proof
kind: route
title: Twist the second GL5 packet alphabet by inverse transpose and replay the exact masks
target: atlas-a4-gl5-dual-packet-collision-screen
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-a8-index-91-to-496-reaches-standard-l5
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas-a4-gl5-dual-packet-collision-screen.json
---

The replay adds one operation to the established `GL5(2)` screen: every
factor-two `4 x 4` label `g` in both the packet and collision word is replaced
by `g^(-T)`.  It then uses the same exact line--complementary-hyperplane
representatives for `GL5(2)/H`, the same 20,160 internal alignments in each
coset, and the same order-two/order-three conjugacy-class masks.

All packet constraints are tested before collision.  The replay invariants
assert 202 packet positions, the intersection histogram in `(GL5-D3)`, the
collision order histogram in `(GL5-D3)`, and zero identity collision values.
No random sampling or floating-point arithmetic occurs.

The run used one MSI CPU with the warm Python dependencies and completed in
under 70 seconds.  The saved JSON is the exact asserted output.
