---
rg: 2
id: type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups
kind: claim
title: Every group acting freely, with finitely many orbits and not type-preservingly, by type rotating automorphisms on the vertices of a thick Ã₂ building embeds in a finitely presented simple group; this includes every CMSZ group and the vertex-regular lattices of the 65 exotic CMSZ buildings of order 3
distinct_from:
  vertex-free-type-rotating-a2-groups-satisfy-boone-higman: that is the whole vertex-free type rotating class; this is its type-transitive part, where every premise of the Li–Matui route is now proved (lane proofs) except the unpinned k-graph standard facts.
  exotic-a2-lattices-satisfy-boone-higman: that is every cocompact lattice on an exotic Ã₂ building; this covers the ones acting freely and type-transitively on vertices, such as the CMSZ groups.
  cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive: that is seven explicit instances certified by computer; this is the general statement.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (2026-09-18) by route `type-transitive-a2-bh-via-rs-two-graph-full-groups`. Every step is a lane proof or an import pinned at source; none is independently reviewed. The last input, `finite-k-graph-boundary-groupoid-standard-facts`, is proved by `finite-k-graph-standard-facts-proof`. Route:
`type-transitive-a2-bh-via-rs-two-graph-full-groups`.

**Statement.** Let `B` be a locally finite thick Ã₂ building, and `Γ` a group of type
rotating automorphisms acting freely on the vertices with finitely many orbits, whose
type-rotation character `θ: Γ -> Z/3` is nonzero. Then `Γ` embeds in an infinite finitely
presented simple group, which is of type `F_∞`.

**Examples.**
- Every CMSZ group `Γ_T`: vertex-regular groups are type-transitive.
- In particular, the lattices of the 65 exotic Ã₂ buildings of order 3 constructed by
  Cartwright–Mantero–Steger–Zappa, which Bader–Caprace–Lécureux list in their review
  (arXiv:1608.06265, §`sec:ReviewExotic`, read at source).
- By BCL these groups have only finite linear images, so no linear Boone–Higman route
  reaches them (`exotic-a2-lattices-satisfy-boone-higman`).
- Every subgroup of such a `Γ` inherits the conclusion, including the type-preserving kernel
  `ker θ`.

**Scope.**
- The type-preserving case `θ = 0`, for groups with no type-transitive overgroup, is not
  covered. There `M_1` and `M_2` have period 3. A variant of the route is sketched in
  `research/artifacts/gq-bh-bh-groupoid-frontier.md` §6: work with the index-3 degree
  lattice `L = {(a,b) : a + 2b ≡ 0 mod 3}` and the phase-0 cylinder set. It is not claimed.
- Lattices with torsion are not covered.
