---
rg: 2
id: arithmetic-star-packet-host-splits-inner-action-gauge
kind: claim
title: The S9 packet host splits as a direct product and exposes the full P multiplicity gauge
distinct_from:
  packet-kazhdan-commutant-placement-decouples: That gives a generic tensor-product countermodel when a packet merely centralizes source subgroups; this identifies the exact gauge already intrinsic to the arithmetic star-packet semidirect host.
  two-fixed-packet-reynolds-actions-leave-a-gram-spectator: That concerns amplification spectators for two fixed packet algebras; this computes the inner-action splitting and the source embedding for this one concrete carrier.
artifacts:
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

Let `theta:P->K=S_9` be the affine permutation action.  Since the action of
`P` on `K` is `Ad(theta(p))`, there is an isomorphism

```text
K rtimes_(Ad theta) P  ~=  K times P,
(x,p) |-> (x theta(p),p).
```

Under this isomorphism the original source embedding sends
`p |-> (theta(p),p)`.  Equivalently `c_p=theta(p)^(-1)p` is a copy of `P`
centralizing `K`.  Thus packet exactification leaves a full representation
of `P` in the packet multiplicity commutant; the internal Reynolds gap does
not automatically lie between the external parent and child Kazhdan low
spaces.

