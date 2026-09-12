---
rg: 2
id: atlas-two-holonomy-endpoint-localization
kind: claim
title: The two t30 bridge holonomies are cross-component endpoint products
artifacts:
  - experiments/atlas_a4_packet_component_audit.py
distinct_from:
  atlas-t30-is-one-parabolic-c3-bridge: that proves the group identity t30=c^-1 a c and its metric consequences; this locates the four letters h,k,z,b on the packet pair graph and therefore specifies what a multiplicity-wire compiler must transport.
---

Use the canonical labels of `atlas-t30-is-one-parabolic-c3-bridge`, so

```text
c=hk,       a=zb.
```

In the exact `K_(2,2) disjoint_union K_(2,4)` decomposition of the A4 packet:

1. `h` is an order-three vertex of the `K_(2,2)` component;
2. `k` is an order-three vertex of the `K_(2,4)` component;
3. `z` is the central order-three vertex of the `S3 x C3` subgroup generated
   by the `K_(2,4)` component; and
4. the collision involution `b` is not one of the ten packet vertices.

The exact matrices are

```text
h = 01000000000101000001000000000001,
k = 01010000010000000000010000000001,
z = 01000000000100000000010100000100,
b = 01000000000100000000010100000001.
```

Consequently `c=hk` is the product of one order-three endpoint from each of
the two disconnected packet components, while `a=zb` is the product of a
`K_(2,4)` endpoint with the collision-only involution.  Neither `c` nor `a`
is one of the four packet rectangle holonomies.  The rectangles remove the
internal cycle gauge; a successful compiler must additionally transport the
two component root gauges to these four endpoints and then evaluate the
collision readout.

This rules out the tempting but incorrect identification of an individual
rectangle variable with `c` or `a`.
