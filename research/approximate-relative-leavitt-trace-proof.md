---
rg: 2
id: approximate-relative-leavitt-trace-proof
kind: route
title: Compare the two cyclic traces of the approximate one-to-two module equivalence
target: approximate-relative-leavitt-cell-kills-active-trace
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

Cyclicity changes each `tr(S_iT_i)` to `tr(T_iS_i)`.  Cauchy--Schwarz for
the normalized trace bounds the scalar error by the normalized
Hilbert--Schmidt error.  Summing the two diagonal relations compares the
trace of `S_0T_0+S_1T_1` with `2tr(P)`; the range-sum relation compares the
same scalar with `tr(P)`.  Their difference is `tr(P)`, proving `(ARL2)`.
