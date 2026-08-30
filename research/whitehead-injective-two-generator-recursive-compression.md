---
rg: 2
id: whitehead-injective-two-generator-recursive-compression
kind: claim
title: Countable recursive groups compress to two generators without losing Whitehead classes or torsion orders
distinct_from:
  whitehead-injective-torsion-order-preserving-higman-embedding: that starts with a finitely generated recursively presented group and ends with a finitely presented group; this starts countably generated and only compresses to a two-generator recursive presentation.
  whitehead-universal-group-via-effective-hnn-and-rope: that applies the construction to a particular universal torsion-free free product; this is the reusable compression theorem for an arbitrary recursively presented group, with or without torsion.
  hnn-torsion-orders-equal-base-torsion-orders: that controls torsion in a given HNN extension; this builds the effective HNN extension and also proves Whitehead injectivity.
---

Every countably generated recursively presented group `Q` embeds in a
two-generator recursively presented group `E` such that

```text
Wh(Q) -> Wh(E)
```

is injective and

```text
Tord(E) = Tord(Q).
```

**ESTABLISHED 2026-08-30** by
[[whitehead-injective-two-generator-free-edge-hnn-proof]].
