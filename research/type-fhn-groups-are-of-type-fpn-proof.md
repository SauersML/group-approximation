---
rg: 2
id: type-fhn-groups-are-of-type-fpn-proof
kind: route
title: "FH_n implies FP_n through the cellular chains of a free replacement"
target: type-fhn-groups-are-of-type-fpn
requires:
  - proper-and-free-type-fhn-coincide
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
---

1. By `proper-and-free-type-fhn-coincide` there is a free `(n−1)`-acyclic
   `G`-CW complex `W` with finitely many orbits of cells.
2. Its cellular chain complex gives `C_n(W) → ⋯ → C_0(W) → ℤ → 0`. This is
   exact at `C_{n−1}, …, C_0` and at `ℤ`, because `W` is `(n−1)`-acyclic.
   Each `C_i(W)` is free on one generator per orbit of `i`-cells.
3. Extending by any free resolution of `ker(C_n → C_{n−1})` gives a free
   resolution of `ℤ` that is finitely generated in degrees `≤ n`.

Theorem A of `research/artifacts/zp-fpn-fhn-2026-09-13-part1.md`, §3.
Unreviewed.
