---
rg: 2
id: edgeful-or3-link-closes-first-chord
kind: route
title: Use the balanced private-plane OR3 packet and eliminate every occurrence pivot
target: first-cycle-signed-hecke-chord
requires:
  - edgeful-or3-balanced-private-plane-packet
  - edgeful-or3-coefficient-link-compiler
  - overlap-subdivision-preserves-coherent-piece-obstruction
---

The open compiler aligns the root skeleton, makes all nonroot overlap
relations triangular in occurrence-private pivots, preserves the finite
packet, and leaves a common phase outside it.  The resulting context
partitions satisfy the old tree overlaps and the new chord literally, while
one assignment projection remains non-root.  These are exactly the
requirements of `first-cycle-signed-hecke-chord`.

The subdivision audit is included to prevent replacing the finite
root-skeleton certificate by macro high girth alone.
