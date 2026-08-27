---
rg: 2
id: atlas-a4-gl5-dual-packet-collision-screen
kind: claim
title: The opposite graph-parity A8 class in L5(2) has no packet-plus-19243 realization
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas-a4-gl5-dual-packet-collision-screen.json
distinct_from:
  atlas-a4-gl5-packet-collision-screen: that applies the same exact coset mask to equal natural-module labeling parity; this applies inverse-transpose to every second-chart label and closes the missing parity.
  atlas-a8-index-91-to-496-reaches-standard-l5: that classifies all subgroup embeddings in the ambient group but detects two marked parity families; this excludes the remaining one.
---

Embed the first chart as standard `H=diag(GL4(2),1)<GL5(2)`.  For the second
chart apply the outer graph automorphism

```text
alpha(g)=g^(-T)                                      (GL5-D1)
```

before conjugating by an arbitrary `h in GL5(2)`.  This exhausts the opposite
relative label parity isolated by the finite-simple overgroup classification.

The exact staged screen over all `496*20160=9999360` relative frames finds

```text
packet survivors                         202,
packet plus q_19243 survivors               0.        (GL5-D2)
```

Indeed the full distribution agrees with the natural-parity screen:

```text
q_19243 order 2                         157,
q_19243 order 4                          45,
intersection sizes 168,1344,20160     118,54,30.      (GL5-D3)
```

Thus no opposite-parity marked pair realizes the packet and collision;
adding q14 cannot restore a solution.

