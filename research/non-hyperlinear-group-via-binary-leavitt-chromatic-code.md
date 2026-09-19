---
rg: 2
id: non-hyperlinear-group-via-binary-leavitt-chromatic-code
kind: route
title: A bounded-area Leavitt chromatic commutator code makes the Steinberg group nonhyperlinear
target: non-hyperlinear-group
requires:
  - binary-leavitt-bounded-area-chromatic-code
  - chromatic-mark-codes-are-metric-agnostic
---

Take the code supplied by `binary-leavitt-bounded-area-chromatic-code` for
`z=x_13(s_1t_1)` in the fixed finite presentation of
`Delta=St_20(L_(F_2)(1,2))`.  By `chromatic-mark-codes-are-metric-agnostic`,
the code kills `z` in every normalized-Hilbert--Schmidt approximation of
`Delta`.  Since `z!=1`, `(MA2)` shows that `Delta` is not hyperlinear.

This route records a calibration, not progress toward
`non-hyperlinear-group`.  The hole it needs is route 5 of
`property-t-free-leavitt-full-mf-radical`, and that route is at least as
strong as the first nonhyperlinear group.
