---
rg: 2
id: signed-free-word-count-forces-linear-return-area
kind: route
title: Compare a linear signed-word count with bounded contributions of relator conjugates
target: power-return-certificates-have-linear-area
requires: []
artifacts:
  - research/artifacts/power-return-certificates-have-linear-area-2026-09-08.md
---

Cyclically reduce the cursor to `v`. A nonempty cyclically reduced
word cannot be a rotation of its inverse: the resulting reflection
of cyclic letter positions would fix a letter or exchange adjacent
inverse letters. Thus the signed count of `v` in `v^m` is at least
`m`, while its value on `v` is one.

A reduced join changes this count by at most `|v|-1`. Three joins
around maximal free cancellation give defect at most
`D=max(1,3(|v|-1))` for arbitrary multiplication. Conjugation then
changes it by at most `2D`. The power-return word has count at most
`1+3D-m`.

Every conjugate of a relator or its inverse has absolute count at
most `M+2D`; a product of `N` such factors has absolute count at
most `N(M+3D)`. Comparing the bounds proves the linear area estimate
uniformly over the conjugating word.
