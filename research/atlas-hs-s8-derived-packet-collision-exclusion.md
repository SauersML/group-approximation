---
rg: 2
id: atlas-hs-s8-derived-packet-collision-exclusion
kind: claim
title: The A4 packet and collision 19243 exclude the S8-derived A8 equality family in HS
artifacts:
  - experiments/atlas_hs_s8_double_cosets.py
  - experiments/atlas-hs-s8-double-cosets.json
  - experiments/atlas_hs_a4_packet_screen.py
  - experiments/atlas-hs-a4-packet-screen.json
distinct_from:
  atlas-hs-equality-escape-must-cross-s8-maximals: that removes only the identity normalizer cell abstractly; this screens every nonidentity S8 double-coset cell.
  atlas-a4-19243-classical-collapse: that treats two automorphism markings of one A8; this also excludes distinct S8-derived A8 subgroups in HS.
---

Fix the maximal `M~=S8<HS` in the official ATLAS degree-1100 action and put
`H=M'~=A8`.  The exact double-coset decomposition is

```text
M\HS/M subdegrees:             1,   28,  105,  336, 630,
|M intersection M^g|:     40320, 1440,  384,  120,  64,
|H intersection H^g|:     20160,  720,  192,   60,  16.       (HSD1)
```

The four nonidentity cells have derived intersections of types respectively
`S6`, `(((C2^3):(C2^2)):C3):C2`, `A5`, and `C2 x D8`.  In every nonidentity cell the two derived
subgroups generate all of `HS`.

Use the official degree-100 ATLAS generators and the exact maximal-subgroup
SLP `HSG1-max5W1` to realize `M` and `H`.  Under any isomorphism
`GL4(2)->H`, the thirty packet words reduce to sixteen distinct **factor-
oriented** pair-cube relations.  Screening the full conjugacy fiber from one
seed relation gives

```text
|M intersection M^g|       40320   1440   384   120   64
packet survivors               60      0     0     0    0
packet plus q_19243              0      0     0     0    0
packet plus q14                 21      0     0     0    0.   (HSD2)
```

Thus the packet itself forces `g` into the identity `M` double-coset.  The
remaining sixty conjugators are exactly the established thirty inner and
thirty graph-marked classical alignments, and collision 19243 kills all of
them.  There is consequently no marked pair of S8-derived A8 subgroups in
`HS` satisfying packet plus collision 19243, hence none satisfying the
stronger packet-plus-19243-plus-q14 system.

The factor orientation in (HSD2) is load-bearing.  If one names each edge
only by its order-two and order-three letters, regardless of which free
factor carries them, the packet falsely collapses from sixteen to twelve
relations and produces spurious same-normalizer survivors.  The replay
assertions explicitly fence that error.
