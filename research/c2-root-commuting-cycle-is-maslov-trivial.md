---
rg: 2
id: c2-root-commuting-cycle-is-maslov-trivial
kind: claim
title: The unique nonchordal C2 root-commuting cycle has trivial Deligne holonomy
artifacts:
  - research/artifacts/c2-root-commuting-graph-maslov-audit-2026-08-21.md
distinct_from:
  c2-root-chart-maslov-holonomy-gap: that proposed synchronizing chordal commuting-root charts into a cycle carrying the order-three Maslov scalar; this proves that the multiplier splits on the entire root graph product, so its unique induced cycle carries no such scalar.
  maslov-finite-subgroup-atlas-no-go: that constructs compatible projective-regular multiplicities on arbitrary finite subgroup atlases; this is an explicit splitting theorem for the infinite cyclic root graph product.
---

Let `G_com` be the commuting graph on the eight `C2` roots in Kassel's
Steinberg presentation of `Sp4(Z)`, and let `A(G_com)` be the graph product of
the eight cyclic root groups.  The graph has four maximal triangles and one
unique induced cycle, on the long roots

```text
beta -- (2alpha+beta) -- (-beta) -- (-(2alpha+beta)) -- beta.
```

Nevertheless the canonical map `A(G_com) -> Sp4(Z)` lifts through the
universal central extension and hence through the three-fold Deligne cover.
Consequently the mod-three Meyer--Maslov multiplier restricts to zero on the
whole graph product.  In particular its holonomy around the unique induced
cycle is trivial and cannot be changed to a nontrivial scalar by a
coboundary gauge.

The proof and full edge table are in
`c2-root-commuting-cycle-splitting-proof`.

