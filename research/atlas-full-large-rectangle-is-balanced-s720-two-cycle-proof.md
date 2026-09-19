---
rg: 2
id: atlas-full-large-rectangle-is-balanced-s720-two-cycle-proof
kind: route
title: Replace the order-seven A8 branch by the faithful A5 rectangle vertex
target: atlas-full-large-rectangle-is-balanced-s720-two-cycle
requires:
  - atlas-large-k22-has-faithful-a5-completion
  - atlas-forward-core-triangle-has-faithful-q96-completion
  - atlas-shared-forward-fan-is-2four-by-3two
---

Use four finite vertices

```text
L=A5,              |L|=60,       full large K2,2 rectangle,
F'=S3 x S3,        |F'|=36,      first packet vertex,
J=S4,              |J|=24,       noncentral collision vertex,
C=C2^4:C3^2,       |C|=144,      forward fan vertex.       (720-1)
```

Their marked incidences are

```text
L--F' over <r,u>~=S3,        L--J over <t,s>~=S3,
F'--C over <r,z>~=C3^2,      J--C over <b>~=C2,
F'--J over <c>~=C2.                                      (720-2)
```

Take `12,20,30,5` copies of their regular actions, respectively.  All have
degree 720.  The five restrictions in `(720-2)` match with multiplicities

```text
120 Reg(S3),       120 Reg(S3),       80 Reg(C3^2),
360 Reg(C2),       360 Reg(C2).                         (720-3)
```

Thus any spanning tree in the incidence graph glues faithfully by permutation
conjugacies.  Since the graph has four vertices and five edges, exactly two
independent edge identifications remain.  The calculation proves marginal
feasibility only; it does not assert that the two holonomies can be killed
simultaneously.
