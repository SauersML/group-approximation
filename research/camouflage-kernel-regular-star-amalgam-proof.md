---
rg: 2
id: camouflage-kernel-regular-star-amalgam-proof
kind: route
title: Read the split kernel from the Bass--Serre quotient tree
target: camouflage-kernel-is-a-regular-star-amalgam
requires:
  - mf-camouflage-surgery
---

Let `W=C_d(Q)` and `K=ker(pi_Q)`.  The Bass--Serre tree of

```text
W=B *_D (Q x D)
```

has vertex sets `W/B` and `W/(Q x D)` and edge set `W/D`.  Since `K` is
normal and `W/K=Q`, its quotient graph has:

* one `(Q x D)`-type vertex, because `pi_Q(Q x D)=Q`;
* one `B`-type vertex for each `q in Q`, because `pi_Q(B)=1`;
* one edge for each `q in Q`, joining the central vertex to the vertex `q`.

This quotient graph is a star and hence a tree.  Its central vertex
stabilizer is

```text
K intersect (Q x D)=D,
```

the stabilizer at the vertex `q` is `qBq^(-1)=B_q`, and every edge
stabilizer is `D`.  Elements of `Q` commute with `D` in the direct-product
vertex, so all edge maps into the central group are the identity and the
copies of `D` in the groups `B_q` are literally the same subgroup.  The
Bass--Serre fundamental-group theorem now gives `(RSA1)`.  The same
description follows directly from the amalgam normal-form theorem.

The canonical section `Q->Q x D->W` splits `pi_Q`, giving `(RSA2)`, and
conjugation by `r in Q` sends the vertex group indexed by `q` to the one
indexed by `rq`.  It fixes `D` because the two factors of `Q x D` commute.

For a homomorphism `f:K->M` with `M` MF, every restriction
`f|_(B_q)` is trivial because `B_q` is isomorphic to the full-radical group
`B`.  The star vertex groups generate `K`, proving `(RSA3)`.  If `B` is
perfect, then each `B_q` lies in `[K,K]`; since they generate `K`, one has
`K=[K,K]`.

