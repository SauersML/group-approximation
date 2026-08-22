---
rg: 2
id: maximal-noncrossing-forest-criterion-proof
kind: route
title: Characterize mergeable blocks by their common noncrossing face
target: maximal-noncrossing-forest-criterion
requires:
  - minimum-block-noncrossing-enumeration-is-not-exhaustive
---

Represent a noncrossing partition recursively as an ordered forest of its
top-level blocks, with one child forest in every gap between consecutive
vertices of a block.  Two blocks can be merged without introducing a crossing
exactly in either of two situations:

1. they are top-level blocks of the same forest; or
2. one is a block and the other is top-level in one of its child forests.

Indeed these pairs share a complementary face, so their union is
noncrossing.  Conversely, for any other pair, their least common ancestor
contains a separating block boundary; joining the pair crosses that boundary.

It follows that a monochromatic merge is available exactly when some forest
has two top-level blocks of the same color, or some child forest has a
top-level block with its parent's color.  Negating these two conditions gives
the stated recursive criterion.  In particular forest width is at most the
number of coefficient copies (four here), which is the key pruning absent
from minimum-block enumeration.

The artifact implements the recursion directly.  As a finite audit, its
output was compared with brute-force coarsening maximality for every
three-color word through length eight; the two sets agree in every case.
