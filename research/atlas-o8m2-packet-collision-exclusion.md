---
rg: 2
id: atlas-o8m2-packet-collision-exclusion
kind: claim
title: Packet plus collision 19243 excludes the O8-(2) equality group
artifacts:
  - experiments/atlas_o8m2_a4_packet_screen.py
  - experiments/atlas-o8m2-a4-packet-screen.json
distinct_from:
  atlas-o8p2-ten-marked-packet-collision-screens-are-empty: that screens six triality A8 classes in the plus-type group; this screens the single centralizer-C3 class in the minus-type group.
  atlas-a4-sp6-packet-collision-screen: that covers only the shared-Sp6 cell; this also excludes all three full-ambient cross-carrier cells.
---

No two marked `A8` charts in `O8-(2)` satisfy the sixteen directed Atlas
packet edges together with collision `19243`.  The exact normalizer-cell
survivor table is

```text
subdegree       packet    packet+19243       collision orders
     1             180          0             2:150, 4:30
    56               0          0             --
   105            1980          0             2:1674, 4:306
   630              72          0             2:36, 4:36
   840             576          0             2:504, 4:72.       (OMS1)
```

In particular, the `56` cross-carrier cell already fails the packet, while
collision `19243` kills every packet alignment in the `630` and `840` cells.
The stronger system containing `q14` therefore has no realization in
`O8-(2)`.

