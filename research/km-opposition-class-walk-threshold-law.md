---
rg: 2
id: km-opposition-class-walk-threshold-law
kind: claim
title: Class-restricted walks in panel-opposition geometries have exactly q to the d minus k components
artifacts:
  - research/artifacts/km-opposition-connectivity-computations-2026-08-23.md
distinct_from:
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that reduces the filtration's relative homology to the twisted opposition combinatorics; this is the connectivity law of those combinatorics, the input for both the surjectivity construction and the small-parameter cokernel theorems.
  km-hexagon-level-cokernel-is-nonzero: that uses the disconnected side of this law at parameters at most three; this is the full two-sided statement with the abstract mechanism.
  km-twisted-level-product-cycles-surject: that is the surjectivity statement consuming this law through the disjoint-class construction; this is pure finite geometry with no homological content.
---

**THEOREM (established; proof in
`km-opposition-class-walk-threshold-proof`).**  Let `Delta` be a
Moufang generalized `m`-gon of order `(q,q)` (`m in {2,4,6}`), `Pi` a
panel (all chambers through a fixed line, say), and `Gamma(Pi)` the
opposition geometry: points at maximal distance from the panel's line,
classed by their gates on it, and lines opposite it.  For a subset `S`
of the `q+1` classes, let `G_S` be the graph on the class-`S` points
and all opposite lines.  Then `G_S` has exactly

```text
q^(max(0, d - |S|))
```

connected components, where `d` is the Frattini dimension of the
unipotent radical `U` of the panel-line's parabolic: `d = 4` for the
split Cayley hexagon line-panels, `d = 3` for symplectic quadrangle
line-panels (abelian Siegel radical), `d = 2` for the point-panels of
either, `d = 2` for grids.  In particular the full geometry is
connected iff `q + 1 > d - 1`... precisely iff `q + 1 >= d`, and
deleting `j` classes preserves connectivity iff `q + 1 - j >= d`.

The law is characteristic-free and is verified computationally at
`q = 2, 3, 4, 5` for the hexagon at every deletion depth, and at
`W(3)` for the quadrangle (artifact).

**Consequence for the program.**  Combined with the disjoint-class
single-slot construction this proves the twisted-level surjectivity of
`km-twisted-level-product-cycles-surject` for `q + 1 >= 2d + 1`
(hexagon levels `q >= 8`), any characteristic, and it delimits exactly
the small parameters where the component-indicator annihilators of
`km-hexagon-level-cokernel-is-nonzero` exist instead.
