---
rg: 2
id: whitehead-injective-two-generator-recursive-compression
kind: claim
title: Countable recursive groups compress to two generators without losing Whitehead classes or torsion orders
distinct_from:
  whitehead-injective-torsion-order-preserving-higman-embedding: that starts with a finitely generated recursively presented group and ends with a finitely presented group; this starts countably generated and only compresses to a two-generator recursive presentation.
  whitehead-universal-finitely-presented-torsion-free-group: that applies the construction to a particular universal torsion-free free product and then passes to finite presentation; this is the reusable two-generator recursive compression theorem for an arbitrary recursively presented group, with or without torsion.
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

If `Q` is finitely presented, then `E` can be chosen finitely presented as
well. Thus the construction also compresses finite presentations to two
generators without losing Whitehead classes or changing torsion orders.

**ESTABLISHED 2026-08-30** by
[[whitehead-injective-two-generator-free-edge-hnn-proof]].
