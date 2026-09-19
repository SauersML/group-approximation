---
rg: 2
id: atlas-m24-packet-survivors-share-octad-and-19243-kills-all
kind: claim
title: In M24 the Atlas packet confines both A8 charts to one octad and collision 19243 kills every survivor
artifacts:
  - experiments/atlas_m24_a4_packet_screen.py
  - experiments/atlas-m24-a4-packet-screen.json
distinct_from:
  atlas-a4-m23-packet-double-coset-screen: that confines packet survivors to one chart inside M23; here a second 15-point same-octad cell survives the packet before collision kills it.
  atlas-o8m2-packet-collision-exclusion: that screens five normalizer cells in O8-(2); this screens all eighteen anti-flag cells in M24.
---

Fix a marked chart `A~=A8<M24`.  For either relative marking parity, inner or
graph, the sixteen factor-oriented Atlas packet edges have exactly `57`
relative-conjugator survivors.  They occur only in two nongenerating cells:

```text
same chart, subdegree 1:                 30 survivors,
same octad, distinct complement,
  subdegree 15:                          27 survivors. (M24P-1)
```

Every one of the thirteen generating cross-octad cells has zero packet
survivors.  Thus the packet alone already forbids a generating marked pair
in `M24`.

Collision `19243` additionally kills all `57` residual survivors in both
parities.  Its nonidentity order histograms are

```text
same chart:        order 2: 25, order 4: 5,
same octad cell:   order 2: 22, order 4: 5.          (M24P-2)
```

For calibration, each parity explicitly replays `5806080` seed-edge
conjugators.  The q14 survivor totals are `19` in inner parity and `20` in
graph parity, while the joint collision-plus-q14 total is zero.

