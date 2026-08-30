---
rg: 2
id: stw82-spectral-interval-band-depth-reuses-colours-proof
kind: route
title: Colour the interval supergraph at its maximum depth
target: stw82-spectral-interval-band-depth-reuses-colours
requires:
  - stw82-indivisible-order-zero-reuse-is-graph-colouring
---

Form the interval-intersection graph `H` on `V`: two vertices are adjacent
when their closed intervals meet.  A finite interval graph of depth at most
`d` is `d`-colourable.  One direct proof orders the intervals by increasing
left endpoint and assigns each interval a colour unused by the intervals
which are still active at that endpoint.  Including the new interval, at
most `d` intervals are active by (B2), so one of `d` colours is available.

The actual support-overlap graph `G_phi` is a subgraph of `H`.  Indeed, if
`J_v` and `J_w` are disjoint, (B1) and functional calculus give

```text
phi_v(1)phi_w(1)=f_v(h)f_w(h)=(f_v f_w)(h)=0.          (B4)
```

Thus a proper `d`-colouring of `H` is also a proper `d`-colouring of
`G_phi`.  The support-graph reuse theorem now says that the maps of each
colour directly sum to one cpc order-zero map.  This proves the first
assertion.

For the consequence, apply the same partition to the finite-dimensional
summands in each approximation.  Neither the incoming map, the outgoing
maps, nor the approximation error changes.  The outgoing map now has `d`
cpc order-zero restrictions, so the definition of nuclear dimension gives
`dim_nuc(A)<=d-1=r`, proving (B3) without an extra colour.
