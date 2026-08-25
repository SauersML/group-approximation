---
rg: 2
id: binary-leavitt-first-mismatch-closes-chromatic-code
kind: route
title: Feed the uniform first-mismatch cell into the canonical Morita complete graphs
target: binary-leavitt-bounded-area-chromatic-code
requires:
  - binary-leavitt-first-mismatch-morita-area-cell
  - binary-leavitt-canonical-morita-tree-reduction
---

The first requirement supplies `(MTR4)` with one constant for both unequal
branch pairs.  The second requirement then applies that constant after free
removal of every longest common prefix, supplies the diagonal conjugate cells
from `(MTR3)`, and uses the complete graphs on `{0,1}^n`.  These are exactly
`(CCC1)--(CCC2)` with depth-independent constants, proving the target.
