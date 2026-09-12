---
rg: 2
id: pure-dyadic-iwahori-linear-repair-proof
kind: route
title: Use slot conservation to discard the deep mass and repair the bottom diagram
target: pure-dyadic-iwahori-pairs-have-uniform-linear-repair
requires:
  - pure-dyadic-clifford-slots-have-a-uniform-one-third-gap
  - fixed-finite-restriction-diagrams-have-linear-hs-repair
---

Let `epsilon` be the edge-generator defect and project the identity matrix
onto the exact edge-intertwiner space. The uniform congruence Poincare
inequality gives an intertwiner `A` with

```text
||I-A||_2<=delta:=epsilon/kappa_B.                       (PDP1)
```

The polar support of `A` is a common edge subrepresentation of physical
rank at least `(1-delta^2)d`. Let `b_+`,`b_-` be the bottom (conductors zero
and one) physical dimensions. Applying `(DCS4)` gives

```text
1-delta^2 <= 2/3+min(b_+,b_-)/(3d),
d-b_+, d-b_- <= 3delta^2 d.                             (PDP2)
```

The bottom/deep conductor decomposition reduces each whole vertex
representation. Replace the deep summand on each side by trivial copies.
The resulting exact vertex representations factor through the fixed
conductor-at-most-one diagram, and each moves by at most

```text
2 sqrt(3)delta.                                         (PDP3)
```

Their edge defect is at most `epsilon+4sqrt(3)delta`. Apply
`fixed-finite-restriction-diagrams-have-linear-hs-repair` to this bottom
diagram. It produces an exactly compatible pair at further distance at
most `C_bot(epsilon+4sqrt(3)delta)`. Combining with `(PDP3)` proves
`(PDR1)--(PDR2)`.

