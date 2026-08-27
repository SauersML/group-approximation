---
rg: 2
id: leavitt-d4-l14-seven-syllable-splitter-proof
kind: route
title: Enumerate maximal noncrossing blocks of the alternating seven-syllable word
target: leavitt-d4-l14-seven-syllable-splitter
requires:
  - leavitt-d4-l14-profile-has-six-rank9-cyclic-classes
---

Write

```text
A1=g2_3 g3_2 g4_3 g5_2 g6_3 g7_2 g8_3.
```

In a free product, `A1=1` precisely when its positions admit a noncrossing
partition into monochromatic blocks, with the ordered coefficient product in
each block equal to one.  Recursing from the first position gives thirty such
partitions.  Removing every partition that strictly refines another leaves
the following five maximal branches:

```text
I:   g3=g5=g7=1,       g2 g4 g6 g8=1;
II:  g3=g6=1,          g5 g7=1,       g2 g4 g8=1;
III: g4=g7=1,          g3 g5=1,       g2 g6 g8=1;
IV:  g4=g6=1,          g3 g5 g7=1,    g2 g8=1;
V:   g5=1,             g3 g7=1,       g4 g6=1, g2 g8=1.
```

Conversely each displayed branch visibly contracts the alternating word to
the identity by the indicated nested cancellations.  The five branches are
therefore exhaustive and reduce the carrier analysis to five cases rather
than thirty.

