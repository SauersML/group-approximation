---
rg: 2
id: atlas-m24-a8-antiflag-cells-have-thirteen-generating-cross-cells
kind: claim
title: M24 has eighteen A8 anti-flag cells, exactly thirteen generating and cross-octad
artifacts:
  - experiments/atlas_m24_a8_antiflag_orbits.py
  - experiments/atlas-m24-a8-antiflag-orbits.json
distinct_from:
  atlas-m24-a8-coset-action-fibers-over-1-8-15: that proves only the three coarse fixed-point fibers; this resolves them into all eighteen A8 double cells.
  atlas-a4-m23-packet-double-coset-screen: that resolves the four cells in the 506-point same-fixed-point fiber only.
---

Identify the unique `A8` class in `M24` with anti-flags `(p,O)`, where `O` is
an octad and `p` is one of its sixteen external points.  The stabilizer
`A=Stab(p,O)` has exactly eighteen orbits on the `12144` anti-flags.

The six cells over the eight-point orbit of `p` have subdegrees

```text
120, 120, 280, 840, 1008, 1680,                     (M24DC-1)
```

and chart-intersection orders

```text
168, 168, 72, 24, 20, 12.                           (M24DC-2)
```

The eight cells over the fifteen-point orbit have subdegrees

```text
15, 105, 120, 630, 840, 1680, 1680, 2520,           (M24DC-3)
```

and intersection orders

```text
1344, 192, 168, 32, 24, 12, 12, 8.                  (M24DC-4)
```

The first cell in `(M24DC-3)` is the same-octad cell: the two complements
lie in one `2^4:A8` carrier.  Together with the four already known same-point
M23 cells, these are precisely the five nongenerating cells.  Every other
cell has distinct fixed points and distinct octads, hence its two charts
generate `M24`.  Thus there are exactly thirteen generating cells, containing
`11623` conjugate charts.

