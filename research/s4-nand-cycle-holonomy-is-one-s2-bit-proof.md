---
rg: 2
id: s4-nand-cycle-holonomy-is-one-s2-bit-proof
kind: route
title: Restrict the standard type to a transposition and multiply the two-sheet edge gauges
target: s4-nand-cycle-holonomy-is-one-s2-bit
requires:
  - s4-standard-corner-realizes-shared-nand-chord
---

A transposition acts in the three-dimensional standard representation with
eigenvalue multiplicities `(+,+,-)`, proving `(NSH1)`.  For two disjoint
transpositions, their simultaneous eigenspaces have ranks

```text
(+,+):1,       (+,-):1,       (-,+):1,       (-,-):0,
```

as in `s4-standard-corner-realizes-shared-nand-chord`.  Hence the shared
minus fiber has no choice, while a rank-one matching of the plus fiber is a
bijection of two points, giving exactly `S_2`.

Changing the ordered plus-sheet basis at a vertex conjugates the incident
edge bijections by that vertex's element of `S_2`.  Choose these vertex
gauges successively along a rooted spanning tree so that every tree edge has
identity matching.  The matching on a non-tree edge is then the ordered
product around its fundamental cycle, namely `(NSH3)`; because `S_2` is
abelian, orientation conventions do not change the bit.

If the product is identity, the transported three rank-one atom labels
return to themselves and the cycle closes.  If it is the swap, it exchanges
the two plus-sheet atoms.  They are orthogonal and carry different values of
the context's second variable, so preserving the labelled endpoint context
forbids the exchange.  This proves `(NSH4)` and identifies the first finite
cycle obstruction.
