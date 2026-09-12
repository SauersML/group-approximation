---
rg: 2
id: decoder-window-fiber-bound-proof
kind: route
title: The decoder reads the fixed output pattern at every interior site, so fibers agree on the interior coordinates
target: decoder-window-fiber-bound-loses-exactly-the-boundary
requires: []
artifacts:
  - research/artifacts/window-balance-mass-transport-2026-09-12.md
---

Section 3 of the artifact. Two inputs in the fiber of `p`, extended by a common exterior, have the
same output on `E`. For `g` in `int_N E` the decoder reads only outputs on `gN`, contained in `E`, so
both inputs agree at `g`. Injectivity forces `1 in NM`, so `g` lies in `EM` and is a fiber coordinate.
The fiber therefore sits in a coset of the `|int_N E|` interior coordinates.
