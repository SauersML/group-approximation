---
rg: 2
id: marker-flip-control-disjointness-proof
kind: route
title: Distance bound on integer-marker positions by case analysis on the 001 | 100 pattern
target: marker-flip-cells-avoid-all-marker-control-windows
requires: []
artifacts:
  - research/artifacts/marker-stable-formalization-residue-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

This is a direct finite case analysis, with the full argument in the claim node and Section 1 of the
artifact. A marker at `i` fixes `x_(i-1) = x_(i+1) = 1` and `x_(i±2) = x_(i±3) = 0`. A marker at `i + d`
needs `x_(i+2) = 1` for `d = 1` or `3`, `x_(i-1) = 0` for `d = 2`, and `x_(i+1) = 0` for `d = 4`. Each
clashes with the marker at `i`, and the reflection symmetry of `001 | 100` closes `d < 0`.

Invariance of the marker set under partial flips then takes two lines. An active window contains no
flipped cell, so its marker survives. A newly created marker would lie within distance 3 of a flipped
marker, and that marker survives too, which contradicts the bound. No external input is used.

**Verification (w3-vf-nonlinear, 2026-09-12): valid.** The distance bound, its sharpness and the
invariance of the marker set under partial flips were re-derived independently. The reverse-inclusion
gap flagged on 62f488374 is closed at 9cb380bf4
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 27).
