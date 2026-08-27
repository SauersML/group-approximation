---
rg: 2
id: leavitt-area-ten-five-digon-proof
kind: route
title: Restore labels on the unique five-cycle of digon gadgets
target: leavitt-area-ten-five-digon-cycle-fails
requires:
  - leavitt-area-ten-short-atlas-partitions
---

Use the rooted ribbon involution

```text
[24,22,21,15,20,19,12,17,16,14,13,23,6,10,9,
 3,8,7,27,5,4,2,1,11,0,29,28,18,26,25].                (A10C1)
```

With the standard cyclic rotation on each consecutive triple, its face
lengths are `10,10,2,2,2,2,2`.  Every other connected five-digon core is
isomorphic to this one or its global reflection.

Orient the fifteen edges.  At each vertex retain only the `++-` or `+--`
patterns of an oriented relator; this leaves `3126` global orientations.
The minority position fixes the relator occurrence index.  Assign the two
relator colors at ten vertices, reject an edge joining inverse occurrences
of the same relator, and reduce all seven region words in `Q`.  The original
decagon-first audit checked the two choices of outer decagon.  The completed
all-face audit allows each of the five digons to be outer as well: in every
case a candidate would have exactly six trivial labels and one nontrivial
label.  No coloring has that pattern.  Thus the solution count is zero for
all seven choices of outer face.
