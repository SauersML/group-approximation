---
rg: 2
id: two-pauli-quarter-carriers-have-fixed-reflection-holonomy
kind: claim
title: The two canonical Pauli quarter carriers generate an exact positive-density D8 holonomy packet
artifacts: [experiments/atlas_transported_corner_overlap.py, experiments/atlas-transported-corner-overlap.json]
distinct_from:
  transported-coefficient-corners-share-flat-quarter-carrier: that constructs one carrier; this computes its angle with the branch-transfer carrier.
  fixed-holonomy-on-overlap-pays-relator-energy: that consumes word-level holonomy; this supplies the exact projection packet.
---

The two canonical trace-quarter atlas projections `F,G` satisfy

```text
tau(FG)=1/16, tau(FGFG)=3/64,
||(2F-1)(2G-1)(2F-1)(2G-1)-1||_2^2=1/2.
```

Their reflections generate a literal `D_8`; its negative central cut has
trace `1/8` and supports an exact anticommuting Pauli pair.  This gives a
spectator-stable holonomy packet, but the reflections remain Hecke
polynomials until a group-word decoder exposes them.
