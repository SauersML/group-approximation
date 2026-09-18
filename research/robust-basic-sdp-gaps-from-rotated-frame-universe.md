---
rg: 2
id: robust-basic-sdp-gaps-from-rotated-frame-universe
kind: route
title: Robust basic-SDP gaps at perfect completeness from the value of the rotated-frame universe game and its discretisation
target: rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps
requires: [rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps, rotated-frame-universe-rich-2to1-game-has-vanishing-value]
---

Given `delta`, the vanishing-value claim gives `n` with
`val(U_n) <= delta/2`. For every `eta > 0`, the discretisation theorem, applied
with `min(eta, delta/2)`, gives a finite rich instance with basic SDP
`>= 1 - eta` and value `<= delta`.

The premises can fail separately:

- the discretisation is established and unconditional;
- the vanishing value can fail through a Borel strategy with bounded-below
  value, which is steps (A1) and (A2) of that node.

A failure of the second premise does not refute the target. Other perfect-SDP
universes with no forcing mass could still be witnesses.
