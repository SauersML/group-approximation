---
rg: 2
id: fpbs-kazhdan-groups-have-fixed-price-one
kind: claim
title: Every countably infinite group with property (T) has fixed price one
root: true
distinct_from:
  fpbs-kazhdan-groups-have-cost-one: that imports the Hutchcroft--Pete theorem that some free action has cost one; this asks that every free action, equivalently the Bernoulli shift, has cost one, which Hutchcroft--Pete explicitly leave open.
  fpbs-kazhdan-sparse-spines: that asks for arbitrarily sparse FIID connected spines, one sufficient mechanism; this is the fixed price conclusion itself, reachable by any mechanism.
---

OPEN restricted research target. Let `Gamma` be a countably infinite Kazhdan group. Every free p.m.p. action of
`Gamma` has cost one.

**Status of the literature (checked 2026-09-17).**
- Hutchcroft--Pete, arXiv:1810.11015, abstract: "We prove that every countably infinite group with Kazhdan's property
  (T) has cost 1, answering a well-known question of Gaboriau. It remains open if they have fixed price 1."
- Fraczyk--Mellick--Wilkens, arXiv:2307.01194, abstract: "We prove all probability measure preserving actions of
  lattices in such groups have cost one, answering Gaboriau's fixed price question for this class of groups."
  This covers higher rank semisimple real Lie groups and products of at least two tree automorphism groups, and so
  it covers higher rank Kazhdan lattices.
- Mellick, arXiv:2307.11728: "G₁ × G₂ has fixed price one if G₁ has higher rank, or if G₁ has rank one and G₂ is a
  p-adic split reductive group of rank at least one."
- Neither import is in the graph as a node. Rank one Kazhdan lattices (`Sp(n,1)`, `F_4^{-20}`) and non-linear
  Kazhdan groups, including hyperbolic ones, remain uncovered by these sources.

**Why it matters here.** If it holds, the counterexample strategy of
`fpbs-kazhdan-rankgradient-counterexample-reduction` cannot succeed for any infinite Kazhdan group. A free action of
cost above one is exactly what a positive rank gradient chain would produce.

## Attempts

* **Functional contacts in the weak-containment closure (route
  `fpbs-kazhdan-fixed-price-via-ideal-voronoi-contacts`).** `fpbs-functional-contact-criterion` (OPEN, proof pending referee) reduces
  the target to one geometric statement, `fpbs-kazhdan-ideal-voronoi-contacts-connect`. Find, in some free action
  weakly contained in Bernoulli, a Borel self-map whose components meet pairwise-adjacent along infinitely many
  Cayley edges. `fpbs-ideal-voronoi-descent-limit-exists` (OPEN, proof pending referee) supplies a canonical candidate for every
  finitely generated group, the rootless geodesic-ray descent map of an ideal Voronoi limit. What is missing is
  contact connectivity of its components, or of any other self-map, for Kazhdan groups.
* **Sparse spines.** `fpbs-kazhdan-sparse-spines` together with `fpbs-sparse-spine-cost-bound` is the older
  mechanism. It needs FIID spines and stalls at admissibility, as recorded there.
