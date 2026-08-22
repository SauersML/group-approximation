---
rg: 2
id: atlas-o8m2-packet-collision-screen-proof
kind: route
title: Replay one literal conjugacy seed fiber across the five O8-(2) cells
target: atlas-o8m2-packet-collision-exclusion
requires:
  - atlas-o8m2-a8-pairs-have-five-normalizer-cells
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_o8m2_a4_packet_screen.py
  - experiments/atlas-o8m2-a4-packet-screen.json
---

The replay uses the degree-`119` model of `O8-(2)`, the unique normal `A8`
inside a maximal `(3 x A8):2`, and an exact `GL4(2)` identification.  The
thirty packet words reduce to sixteen factor-oriented edges.  Because the
ambient normalizer induces all of `Aut(A8)`, one conjugator scan covers both
relative graph markings.

Fix the first packet edge `(x,y)`.  The script iterates the literal ambient
conjugacy class of `y`; whenever `(xy')^3=1`, it chooses `g0` with `y^g0=y'`
and enumerates `C_G(y)g0`.  Hence every conjugator satisfying the seed occurs
exactly once.  There are

```text
8,294,400 seed conjugators.                           (OMS2)
```

The other fifteen packet edges leave `2808`; literal multiplication of
collision `19243` leaves zero.  The normalizer-intersection order assigns
each survivor to the independently established cell in `(OMP1)`, producing
`(OMS1)`.  Assertions pin `(OMS1)`--`(OMS2)` and the order histograms.  No
character-table matrix, floating point, sampling, or full ambient scan is
used.

