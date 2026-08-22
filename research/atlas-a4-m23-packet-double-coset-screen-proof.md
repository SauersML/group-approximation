---
rg: 2
id: atlas-a4-m23-packet-double-coset-screen-proof
kind: route
title: Exhaust the four maximal-A8 double cosets in the ATLAS degree-23 M23 model
target: atlas-a4-m23-packet-double-coset-screen
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-q14-simple-overgroup-index-is-at-least-506
artifacts:
  - experiments/atlas_a4_m23_packet_scan.py
  - experiments/atlas-a4-m23-packet-screen.json
---

The replay uses the official [ATLAS degree-23 standard generators for
`M23`](https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M23G1-p23B0) and the
official [maximal-`A8` straight-line
program](https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/M23G1-max4W1).
The script asserts orders `|G|=10200960`, `|H|=20160`, and
`|N_G(H)|=20160` before testing any Atlas relation.

GAP computes `H\\G/H` directly.  Its four cells have the sizes in
`(M23-DC1)` and sum to `|G|`; the intersection orders follow from

```text
|HgH| = |H|^2 / |H cap H^(g^-1)|.
```

The fixed isomorphism `GL4(2) -> H` transports every packet label.  The
second-chart alphabet is tested first unchanged and then after
inverse-transpose.  Since `Out(A8)=C2` and `N_G(H)=H`, these are precisely the
two possible relative marking parities.  Iterating the four double cosets
therefore exhausts every marked conjugate without treating the ambient group
as an unstructured list.

Within a cell, each conjugator is tested against all thirty packet words.
Only packet survivors are evaluated on collision 19243 and q14.  Replay
assertions fix all totals in `(M23-DC2)` and assert that every nonidentity
double coset has zero packet survivors.  All arithmetic is exact permutation
group arithmetic; there is no random sampling or floating point step.  The
hardened MSI replay used one CPU and completed in under 70 seconds.

