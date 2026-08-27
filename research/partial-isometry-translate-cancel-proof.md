---
rg: 2
id: partial-isometry-translate-cancel-proof
kind: route
title: Cancel on the support and bound its orthogonal complement by trace
target: partial-isometry-translate-cancel-charges-first-exit
requires: []
---

For `(PIT2)`, the two row-supported operators `PX` and `(R-P)X` are
orthogonal in `L^2`, while `A^*A=P` gives `||AX||_2=||PX||_2`; the complement
has square at most `||X||_infinity^2 tau(R-P)`.  Cyclicity gives the dual
identity `(PIT4)`.

The four-term decomposition `(PIT7)` and the triangle inequality bound
`||A(B-B')||_2`; inserting that bound into `(PIT2)` proves `(PIT6)`.  The
right-supported decomposition proves `(PIT8)`.  Iterating these two fixed
inequalities through the two translated triangles and the fixed signed-Weyl
words gives `(PIT9)`, with every omitted support recorded as a first-exit
projection.
