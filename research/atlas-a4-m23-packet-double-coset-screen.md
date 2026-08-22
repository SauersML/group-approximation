---
rg: 2
id: atlas-a4-m23-packet-double-coset-screen
kind: claim
title: In the maximal A8 class of M23 the packet forces the two chart subgroups to coincide
artifacts:
  - experiments/atlas_a4_m23_packet_scan.py
  - experiments/atlas-a4-m23-packet-screen.json
distinct_from:
  atlas-a4-gl5-dual-packet-collision-screen: that needs collision 19243 after 202 packet survivors in one L5(2) parity; here the packet itself confines every survivor to the identity A8 double coset.
  atlas-q14-simple-overgroup-index-is-at-least-506: that isolates M23 abstractly as the index-506 boundary; this performs the exact marked double-coset calculation.
---

Let `G=M23` and let `H<G` be its maximal subgroup `H~=A8` of index 506.
Fix a marking `GL4(2) -> H`.  For either relative marking parity, inner or
graph, conjugate the second marked chart by arbitrary `g in G`.

There are exactly four `H`--`H` double cosets.  Their sizes and chart
intersection orders are

```text
|HgH|       20160    302400   4233600   5644800
|H cap H^g| 20160      1344        96        72.       (M23-DC1)
```

The exact packet-first screen gives, in each marking parity,

```text
                                      inner       graph
packet survivors                         30          30
packet survivors outside HgH=H            0           0
packet plus q_19243 survivors              0           0
packet plus q14 survivors                 11          10.       (M23-DC2)
```

Consequently the packet alone forces `g in H`, hence `H^g=H`.  In
particular, no packet-compatible pair of marked maximal `A8` subgroups
generates `M23`.  Collision 19243 separately kills all sixty residual
same-chart markings, so neither adjoining it nor q14 can create an escape.

