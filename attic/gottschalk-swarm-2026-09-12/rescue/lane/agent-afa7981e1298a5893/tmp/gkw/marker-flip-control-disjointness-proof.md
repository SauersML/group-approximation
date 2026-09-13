---
rg: 2
id: marker-flip-control-disjointness-proof
kind: route
title: Distance bound on integer-marker positions by case analysis on the 001 | 100 pattern
target: marker-flip-cells-avoid-all-marker-control-windows
requires: []
artifacts:
  - research/artifacts/marker-stable-formalization-residue-2026-09-12.md
---

Direct finite case analysis; full argument in the claim node and Section 1 of the artifact. The four
cases `d = 1,2,3,4` each expose one cell forced to opposite values by the left `001` context of one
marker and the right `100` context of the other; the left-right reflection of the pattern closes the
negative distances. No external input is used.
