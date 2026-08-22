---
rg: 2
id: leavitt-long-odd-face-core-partitions
kind: claim
title: Area-eight odd faces of lengths eleven through fifteen force two to four gate digons
artifacts:
  - research/artifacts/leavitt-odd-nine-and-long-face-partitions-2026-08-21.md
distinct_from:
  leavitt-area-eight-parity-breaking-dichotomy: that bounds the possible odd lengths by curvature alone; this lists the exact face partitions after lengths five through nine are eliminated.
---

After `leavitt-no-odd-nine-corner-relations`, every area-eight survivor has
exactly one odd internal face.  Up to ordering the four even internal faces,
the complete face-length list is one of

```text
(2,2,2,2,5,11), (2,2,2,3,4,11),
(1,2,2,2,6,11), (1,2,2,4,4,11),
(2,2,2,2,3,13), (1,2,2,2,4,13),
(1,2,2,2,2,15).                                        (LOP1)
```

The first entry in each tuple may be the outer face when it is odd; the
other odd entry is internal.  Thus every length-eleven core has at least two
internal digons, and all but the `(1,2,2,4,4,11)` case have at least three.
Lengths thirteen and fifteen force at least three and four digons,
respectively.

Each internal digon is labelled by a length-two coefficient identity.  The
short coefficient classification says it must be the double traversal of
one of `h_0,h_2,k_0,k_1`.  Contracting these marked gate digons reduces the
length-eleven search to cubic planar cores on at most four vertices in three
of its four partitions, and reduces the length-thirteen/fifteen searches to
at most two-vertex (possibly terminal degenerate) cores.  This is the structural input for the remaining finite
classification.
