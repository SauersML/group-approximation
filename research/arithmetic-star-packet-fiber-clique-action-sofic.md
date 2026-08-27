---
rg: 2
id: arithmetic-star-packet-fiber-clique-action-sofic
kind: claim
title: The ascending-HNN actor acts soficly on the finite-fiber clique graph that untwists the star packet
distinct_from:
  arithmetic-star-packet-carrier: That constructs the packet amalgam and its nontrivial mark; this constructs finite induced-graph models for a larger coset space used only as a sofic envelope.
  arithmetic-star-packet-host-splits-inner-action-gauge: That untwists the packet host abstractly as a direct product; this untwists the stabilizer action equivariantly over every HNN coset.
artifacts:
  - GroupApproximation/Sofic/AscendingHNNCosetActionSofic.lean
  - GroupApproximation/Sofic/SoficActionCyclicExtension.lean
  - GroupApproximation/Sofic/MappingTelescopeFiniteOrbits.lean
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

Let `theta:P->Q=AGL(3,2)<=S_9` be the packet action and put
`L=ker(theta)`.  On

```text
Y=E/L  ->  X=E/P
```

join two distinct vertices precisely when they have the same image in `X`.
Every fiber is a clique of size `[P:L]=|Q|=1344`, and different fibers have
no edges.  The ascending HNN group `E` acts soficly on this graph.

This is stronger than merely knowing that `E` acts soficly on the underlying
set.  For every finite test window, Cairn's telescope proof places the tested
normal-subgroup elements in one telescope level.  That level is commensurable
with `L`, so all of its orbits on `E/L` are finite.  Equip each such finite
orbit with the graph induced from `Y`.  The exact orbit charts are induced-
graph embeddings because the clique relation is `E`-invariant.  Cairn's
cyclic-stack construction then adjoins the stable letter; its charts only
precompose by genuine `E`-translations, so induced adjacency and nonadjacency
remain exact on the tested window.

