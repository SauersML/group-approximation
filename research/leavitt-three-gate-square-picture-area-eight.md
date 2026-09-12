---
rg: 2
id: leavitt-three-gate-square-picture-area-eight
kind: claim
title: A reduced three-gate picture closed only by the forced squares has at least eight cells
distinct_from:
  leavitt-three-gate-kernel-picture-has-area-at-least-six: That exhausts areas two and four by all labelled ribbon pairings; this classifies the area-six cubic planar graph types first and rules out every relator colouring.
artifacts:
  - research/leavitt-three-gate-square-picture-area-eight-proof.md
  - research/artifacts/enumerate-leavitt-three-gate-six-cell-pictures.py
---

In the universal coefficient model

```text
U=<h_0,h_1,h_2,k_0,k_1,k_2 | h_0^2=h_2^2=k_0^2=1>,
```

there is no reduced coefficient-boundary picture with six relator vertices
over the paired three-gate presentation.  Together with the two- and
four-cell census, every square-only kernel picture has at least eight cells.

For the actual Leavitt quotient, a kernel picture of area at most six must
therefore contain an internal region whose label uses a coefficient relation
other than the three forced involution squares.
