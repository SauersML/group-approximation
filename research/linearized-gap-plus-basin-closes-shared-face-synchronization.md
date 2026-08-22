---
rg: 2
id: linearized-gap-plus-basin-closes-shared-face-synchronization
kind: route
title: Enter the mixed-norm tube and use the complete-overlay Jacobian gap
target: repeated-ldpc-shared-face-marginal-synchronization
requires:
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
  - complete-pair-overlay-uniform-hs-basin-capture
---

First use basin capture to pay for the sparse high-operator-norm sector and
place the remaining occurrence tuple in the uniform operator-norm Newton
tube of an exact shared representation.  Equation `(QLS1)` supplies a
dimension-independent inverse transverse to simultaneous conjugation and
multiplicity strata, while `(QLS5)` makes Newton contract in that tube.
The resulting exact occurrence representation has literal shared
marginals, and the initial truncation plus the convergent corrections give
the required normalized-HS modulus.
