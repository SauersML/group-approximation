---
rg: 2
id: atlas-o8p2-ten-marked-packet-collision-screens-are-empty
kind: claim
title: Packet plus collision 19243 excludes every marked A8 pair in O8+(2)
artifacts:
  - experiments/atlas_o8p2_ten_packet_screens.py
  - experiments/atlas-o8p2-ten-packet-screens.json
distinct_from:
  atlas-a4-sp6-packet-collision-screen: that is the same-carrier orthogonal screen inside S6(2); this covers all cross-triality and outside-carrier cells in O8+(2).
  atlas-natural-a8-supports-collapse-before-collision: that treats natural supports in alternating groups; this also covers natural/orthogonal cross-type cells in the triality group.
---

Let `G=O8+(2)`, with natural self-normalized chart classes `N_i` and
orthogonal `S8`-normalized chart classes `O_i`.  For the ten marked screens of
`atlas-o8p2-cross-class-pairs-reduce-to-ten-marked-screens`, the exact survivor
table is

```text
marked pair                    seed fiber   packet    packet+19243
N1--N2, parity 0                1,492,992        0          0
N1--N2, parity 1                1,492,992        0          0
O1--O2                          8,957,952    2,776          0
N1--O1, parity 0                1,492,992        0          0
N1--O1, parity 1                1,492,992        0          0
N1--O2, parity 0                1,492,992        0          0
N1--O2, parity 1                1,492,992        0          0
N1--N1, parity 0                1,492,992      208          0
N1--N1, parity 1                1,492,992      208          0
O1--O1                          8,957,952    2,776          0.       (O8S1)
```

The diagonal screens in `(O8S1)` range over every ambient conjugator, not
merely the outside-carrier residue.  Thus they strengthen the required
diagonal statement.

Every surviving packet alignment has a nonidentity collision witness.  In
the two `O--O` screens the exact order histogram of the value of collision
`19243` is

```text
order 2: 2256,       order 4: 520;
```

and in each marked `N--N` screen it is

```text
order 2: 176,        order 4: 32.                    (O8S2)
```

The replay artifact also records a literal ambient permutation witness for
each nonempty packet screen.  Consequently no pair of marked `A8` charts in
`O8+(2)` satisfies the sixteen directed packet edges together with collision
`19243` (and hence none satisfies the stronger system also containing `q14`).

