---
rg: 2
id: kazhdan-normal-subgroups-of-splittings-and-graph-products
kind: claim
title: Kazhdan normal subgroups of amalgams and HNN extensions lie in the edge core, and in graph products they lie in the universal factor
distinct_from:
  relative-defect-criterion-holds-for-finite-compression-cores: that confines admissible kernels using compressors of the rigid pair; this confines Kazhdan normal subgroups using a splitting of the ambient group.
  graph-product-normal-forms-and-rf-permanence: that imports normal forms and residual finiteness of graph products; this uses normal forms to locate every normal subgroup with property (T).
---

**ESTABLISHED.** Let `M` be a normal subgroup with property (T) of a countable
group `H`.

1. **Splittings.** Suppose either `H = A *_C B` with `C` proper in both `A` and
   `B`, or `H` is an HNN extension of `A` over `C`. Then `M` lies in the normal
   core of `C` in `H`.
2. **Graph products.** Let `H` be the graph product of nontrivial groups `H_v`
   over a finite simplicial graph `Delta`, and let `Z` be the set of vertices
   adjacent to all other vertices. Then `H = H_Z x H_(Delta - Z)` and
   `M <= H_Z`. In particular `M = 1` when `Delta` has no universal vertex.

Derivation: `kazhdan-normal-splittings-graph-products-proof`.

## Consequences for the relative defect criterion

These cases concern `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`.

- **Sofic amalgams and HNN extensions over amenable edge groups.** `M` lies in
  an amenable subgroup and is Kazhdan, so it is finite, and the criterion holds
  (`sofic-quotients-by-finite-normal-subgroups-are-sofic`).
- **Graph products of sofic groups with no universal vertex.** `M = 1`, so the
  criterion is the absolute one, `sofic-groups-kill-rigid-compression-defects`.
- **Any other graph product host.** It can violate the criterion only if
  `H_Z / M` is nonsofic. The quotient `H/M = H_Z/M x H_(Delta - Z)` would carry
  a rigid defect, and the second factor embeds in `H`, hence is sofic. So graph
  products add no counterexample hosts beyond finite direct products of their
  universal vertex groups.
