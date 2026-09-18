---
rg: 2
id: fpbs-kazhdan-ideal-voronoi-contacts-connect
kind: claim
title: Every infinite Kazhdan group carries a contact-connected functional graphing in some free action weakly contained in Bernoulli
distinct_from:
  fpbs-kazhdan-sparse-spines: that asks for a thin FIID connected vertex set; this asks for a full-support self-map, in any action of the weak-containment closure of Bernoulli, whose components touch along infinitely many edges, and it never selects a sparse set.
  fpbs-functional-contact-criterion: that is the proposed implication (written proof, OPEN pending referee) from such a map to fixed price one; this is the open existence of the map for Kazhdan groups.
  fpbs-ideal-voronoi-descent-limit-exists: that is the proposed existence (written proof, OPEN pending referee) of a rootless descent map for every group; this asks that some map, possibly that one, be contact-connected, which fails for free groups.
---

OPEN. Let `Gamma` be a countably infinite group with property (T), `S` a finite symmetric generating set, and
`b_Gamma` its Bernoulli shift. Then there exist a free p.m.p. action `a ≺ b_Gamma` and a Borel self-map `f` with
graph in the orbit relation, such that in almost every orbit the graph on the components of `f`, joining two
components that are linked by infinitely many Cayley edges, is connected. The definitions are those of
`fpbs-functional-contact-criterion`.

**This prerequisite can fail.** By the contrapositive in `fpbs-functional-contact-criterion`, it fails for every group
without fixed price one. So a Kazhdan counterexample to fixed price, as sought in
`fpbs-kazhdan-rankgradient-counterexample-reduction`, would refute it.

**Canonical candidate.** Take the ideal Voronoi descent map of `fpbs-ideal-voronoi-descent-limit-exists`. Its forward
chains are geodesic rays, and its cells are the classes of the tail relation.

**Caveats recorded before any attack.**
- *Rank one geometry.* In real hyperbolic space and in trees, horoballs based at distinct boundary points have bounded
  common border. The Fraczyk--Mellick--Wilkens mechanism relies on higher rank: "these tessellations partition the
  space into ``horoball-like'' cells so that any two share an unbounded border" (arXiv:2307.01194, abstract). For
  hyperbolic Kazhdan groups, such as cocompact lattices in `Sp(n,1)`, the Voronoi candidate is therefore expected to
  fail, and a different self-map would be needed.
- *Components versus cells.* The criterion uses components of `f`, meaning connected components of its graph, not the
  tail-relation cells. For a rootless map with geodesic-ray chains, two points lie in the same component iff their
  chains eventually merge. So components and tail cells coincide here, but only because there are no roots.
- *Unbounded border is not infinite contact.* Two cells can share an unbounded border that is disconnected, or that
  runs within bounded distance without adjacent edges. The discrete statement needs infinitely many Cayley edges
  between the two components.
- *Necessity is open.* It is not known whether fixed price one forces such a map. If it does, this claim is equivalent
  to the target of the route, and the route is a reformulation rather than a reduction.

## Attempts

None yet beyond the calibration in `fpbs-functional-contact-criterion`:
- It succeeds for `F_2 x Z` with `f = z`.
- Descent maps along Cayley edges fail for free groups.
