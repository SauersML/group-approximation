---
rg: 2
id: radius-one-hexagon-probe-omits-regular-packet
kind: claim
title: The radius-one hexagon gauge probe is a thin packet and cannot test the regular character
artifacts:
  - research/artifacts/leavitt-defect-floor-experiment-2026-08-26.md
distinct_from:
  leavitt-regular-character-is-not-mf: that asks whether regular-character operator-norm microstates exist at every radius; this proves that one concrete radius-one numerical bundle omits almost all regular sectors and therefore cannot decide that leaf.
  steinberg-group-is-glued-over-the-permutohedron: that localizes compatibility to braid hexagons for genuine vertex restrictions; this audits one prescribed finite bundle and does not assert that every bundle or the full Steinberg group glues.
---

**ESTABLISHED.**  In the radius-one binary-Leavitt hexagon probe
`hexagon_holonomy.py`, put

```text
V=F_2^5,
W=span{1,s_i,t_i,s_i s_j,s_i t_j,t_i t_j}/<1+e_00+e_11>.
```

Then `dim(W)=16` and the local Heisenberg group has order `2^26`.  The
script constructs a coherent `1024`-dimensional local representation whose
two wall restrictions are the regular representation of `V directSum V`.
However, it chooses only one central-character extension `psi_chi in W^*`
for each of the `32` restrictions `chi in V^*`, and retains only a
`32`-dimensional diagonal selection inside each chosen central sector.

The regular representation uses all `2^16` central characters and has
dimension `2^10` in every central sector.  Thus the probe is not the regular
local packet.  Tensoring it by an arbitrary multiplicity `m` only duplicates
the same thin sector selection; it never restores the omitted central
characters or irreducible multiplicities.

Consequently numerical gauge optimization for this bundle cannot establish
or refute `leavitt-regular-character-is-not-mf`.  The code also does not
check whether the marked element `x_13(q)` survives.  Even an exact
gauge-trivial holonomy would produce at most a representation with these six
prescribed radius-one restrictions, not a regular-character model of the
full Steinberg group.  A positive optimizer residual proves no lower bound.

The original script additionally computed the image of a five-dimensional
linear map by spanning a list of all `32` image vectors, thereby enumerating
`2^32` coefficient tuples.  Since those vectors already exhaust the image,
the correct finite computation is their set (or a row-reduced basis).  This
implementation defect explains the initial remote stall but does not change
the mathematical scope fence above.

DERIVATION
radius-one-thin-hexagon-packet-proof
