---
rg: 2
id: leavitt-degree3-algebraic-corner-cycle-is-absent
kind: claim
title: The full Leavitt packet has no degree-three algebraic corner cycle killing the center
artifacts:
  - research/leavitt-degree3-algebraic-corner-cycle-proof.md
  - research/artifacts/search-leavitt-degree3-postpivot.py
  - research/artifacts/search-leavitt-degree3-two-pivot.sbatch
distinct_from:
  leavitt-degree3-formal-corner-cycle-is-absent: that excludes equality of distinct formal slot words; this tests all exact equalities caused by the actual Leavitt coefficient relations.
  leavitt-degree3-direct-pivot-screen-is-empty: that uses either unary orbit alone; this identifies the second unary corner with the pivot before reducing the target.
---

Across every degree-three, length-eleven `(1,1,9)` topology and every
placement of the full Leavitt packet, no orientation of the unique long target
corner collides with either unary corner so that identifying the two unary
corners, substituting the pivot, and cyclically reducing the target yields the
central involution `[c_i,d_i]` in a coefficient copy.

Combined with the long-corner peeling criterion and the formal topology
screen, this fences the minimal two-relator corner-cycle compiler in degree
three and length eleven.  A next Leavitt design must use a larger long-corner
two-core, not another arrangement of this packet in the same topology.
