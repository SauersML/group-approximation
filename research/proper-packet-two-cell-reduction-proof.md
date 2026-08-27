---
rg: 2
id: proper-packet-two-cell-reduction-proof
kind: route
title: Apply the regular stationary flow and isolate the first nonflat holonomy cell
target: proper-packet-rank-growth-needs-compressed-two-cell
requires:
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

Choose one common integer `L` divisible by every vertex-group order and put
`V_v=(L/|G_v|) lambda_(G_v)`.  Restriction to either endpoint of an edge
group `H_e` is `(L/|H_e|)lambda_(H_e)`.  Hence every proper attachment has
exactly matched finite multiplicity reservoirs.  Iterating along a path or
closing a cycle changes no total edge type and cannot yield a strict
multiplicity inequality.

Therefore any alleged rank pressure must first appear when a two-cell fixes
a product of the otherwise free edge intertwiners.  Exactify the fixed
finite packet groups and decompose that word into its isotypic block maps.
If the relevant initial and terminal carriers have equal rank, the maps are
square and no dimension contradiction follows from rank conservation.

If their ranks differ by `q>0`, write the two cyclic orders of the decoded
block maps as `YX` and `XY`, with carrier projections `E,F`.  Any trace-only
return estimates give

```text
|tr(E)-tr(F)|
 <= |tr(E)-tr(YX)| + |tr(XY)-tr(F)|,                            (1)
```

because `tr(YX)=tr(XY)` in matrices.  Equation `(1)` is precisely the scalar
trace-cyclic checksum.  Relative `C'(lambda)` may make the attaching word
geometrically well behaved, but it does not prove either return estimate in
`(1)`; that is the remaining group-word actuator theorem.

