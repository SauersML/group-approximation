---
rg: 2
id: block-adaptive-balanced-reset-proof
kind: route
title: Reset each central block and integrate the incidence bound
target: block-adaptive-sparse-reset-is-cheap
requires:
  - quadratic-redundant-check-overlay-gives-uniform-face-gap
---

The common reducing property makes `(BAS1)` a reflection and permits every relation energy to
be computed blockwise.  Reset all equality copies together.  Telescope
fixed-width words, count `O(M)` balanced face incidences per coordinate and
`O(L|U|)` complete ordered pairs, then integrate the resulting scalar bound
against the central trace weights.
