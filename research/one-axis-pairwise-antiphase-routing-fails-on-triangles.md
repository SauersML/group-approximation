---
rg: 2
id: one-axis-pairwise-antiphase-routing-fails-on-triangles
kind: claim
title: A one-axis pairwise antiphase router is inconsistent on every triangle
distinct_from:
  affine-source-charts-have-a-disjoint-tag-packing-ceiling: that counts disjoint character packets in one common finite tag group; this is an exact conjugacy-cycle obstruction even when every edge has its own comparison word.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that uses stationary representation-ring flow in a finite graph-of-groups atlas; this is the elementary three-edge sign obstruction for one local operator axis.
---

Let the routing graph contain a triangle on branches `1,2,3`.  Suppose branch
`i` has one satisfying-sector involution `A_i`, one source scalar
`eta_i in {+1,-1}`, and every source comparison word incident to `i` differs
from that one axis only by a power of the marked sign.  Write its action as

```text
on the satisfying sector:       sigma_(i,ij) A_i,
on the failure source F_i:      sigma_(i,ij) eta_i,
```

where `sigma_(i,ij) in {+1,-1}`.  If the edge relation identifies the two
satisfying-sector operators and the two source phases are opposite, then

```text
sigma_(i,ij)A_i=sigma_(j,ij)A_j,                       (OAR1)
sigma_(i,ij)eta_i=-sigma_(j,ij)eta_j.                  (OAR2)
```

Define `B_i=eta_i A_i`.  Equations `(OAR1)--(OAR2)` imply

```text
B_j=-B_i                                                (OAR3)
```

on every edge.  Going around a triangle gives simultaneously
`B_2=-B_1`, `B_3=-B_2=B_1`, and `B_3=-B_1`, a contradiction because an
involution is nonzero.

Therefore the pairwise antiphase route cannot be groupified by reusing one
local involution per branch and inserting marked signs edge by edge.  A live
construction needs at least a genuinely multi-axis joint representation at
each branch, with the edge axes satisfying a nontrivial global compatibility
law, or a finite-dimensional decoder which is not an exact one-axis word
atlas.
