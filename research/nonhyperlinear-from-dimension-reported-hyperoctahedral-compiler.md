---
rg: 2
id: nonhyperlinear-from-dimension-reported-hyperoctahedral-compiler
kind: route
title: Diagonalize against the activated hyperoctahedral predicate table
target: non-hyperlinear-group
requires:
  - dimension-matched-kleene-microstate-diagonal
  - marked-hyperoctahedral-table-linear-dimension-breaker
  - dimension-reported-hyperoctahedral-table-halting-compiler
---

Apply the dimension-matched Kleene theorem to the compiler.  If its fixed
point found a separated microstate and printed its dimension `D`, the
activated hyperoctahedral table would violate `(MHB2)` in that same matrix.
Therefore the fixed point does not halt, its marked word survives, and
hyperlinearity would make the search halt after all.
