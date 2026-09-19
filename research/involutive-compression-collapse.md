---
rg: 2
id: involutive-compression-collapse
kind: claim
title: Pointwise compression collapse of involutive witnesses
distinct_from:
  compression-torsion-collapse: That claim covers witnesses of EVERY finite order; this one is the order-two case alone, proved independently of any projection statement, and it is the base of the acyclic derivation chain (involutive, then projections, then all orders).
artifacts:
  - GroupApproximation/Sofic/InvolutionCollapseEndpoint.lean
---

Let E be countable, L <= E Kazhdan, s a one-sided compressor of L, and
k an involution centralized by the compressed copy whose L-conjugation
orbit commutes pairwise.  Then every collapse commutator `[gamma, k]`,
`gamma in L`, is invisible in every corona representation of E.  This
is the order-two case of the compression collapse, kernel-checked
unconditionally in
`InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness`,
and it is proved with no reference to corona projections: the analytic
input is the displacement almost-cocycle and one-sided Kazhdan
transport alone.  The projection collapse bootstraps from exactly this
case, and the Fourier reduction then returns every higher order — so
this node is the root that keeps the derivation acyclic.
