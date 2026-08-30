---
rg: 2
id: one-relator-two-generator-torsion-spectrum-embedding
kind: claim
title: Every one-relator group embeds in a two-generator one-relator group with the same torsion orders
distinct_from:
  hnn-torsion-orders-equal-base-torsion-orders: that is the generic torsion theorem for an arbitrary HNN extension; this uses a specific Magnus HNN extension to compress a one-relator presentation to two generators.
  one-relator-groups-sofic: that is the still-open approximation claim; this is an unconditional embedding theorem and makes the two-generator reduction exact.
  mikaelian-explicit-higman-embedding: that embeds recursively presented groups into finitely presented groups with many relators; this stays inside one-relator groups and preserves the complete torsion-order set.
---

For every finitely generated one-relator group `G` there is a two-generator
one-relator group `H` and an embedding

```text
G -> H
```

such that

```text
Tord(H) = Tord(G).
```

In particular every finitely generated torsion-free one-relator group embeds
in a torsion-free two-generator one-relator group.

**ESTABLISHED 2026-08-30** by
[[one-relator-two-generator-hnn-embedding-proof]].
