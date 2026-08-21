---
rg: 2
id: bass-serre-marginals-do-not-charge-rank-one-failure-proof
kind: route
title: Separate all finite vertex groups in one finite quotient and use its regular representation
target: bass-serre-marginals-do-not-charge-rank-one-failure
requires:
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - rank-one-no-signaling-pairing-floor
---

A finite graph of finite groups has virtually free, hence residually finite,
fundamental group.  Bass--Serre normal form embeds every vertex group.  There
are only finitely many nonidentity elements in their union, so a product of
finitely many separating finite quotients is injective on every vertex group
simultaneously.

In the regular representation of that quotient, restriction to `G_v` is
`[Q:G_v]` copies of `Reg(G_v)`.  Thus all edge intertwiners and HNN relations
are exact and every complete selector--radical type vector is transported.
The full selector subgroup is also embedded, so each of its Fourier atoms has
trace `1/|D|`.  Applying the rank-one scalar inequality merely locates
positive mass in endpoint types; it cannot make an already exact edge
intertwiner defective.  This is the countermodel `(BMF3)--(BMF6)`.
