---
rg: 2
id: nonfibered-closed-graph-manifold-groups-satisfy-pbh
kind: claim
title: Fundamental groups of closed graph manifolds that are not virtually fibered lie in the permutational Boone--Higman class
distinct_from:
  three-manifold-groups-pbh-off-nonfibered-graph-manifolds: that proves membership in B_A for every compact 3-manifold outside this class; this is exactly the class left over.
  virtually-fibered-3-manifold-groups-satisfy-pbh: that handles graph manifolds with a fibered finite cover; this is the ones with none, where no fibre exists to embed in a mapping class group.
  compact-3-manifold-groups-satisfy-pbh: that is the statement for all compact 3-manifolds; this is its only missing case.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**OPEN.** Let `N` be a closed orientable graph manifold with non-trivial JSJ
decomposition that has no finite cover fibering over the circle. Then `pi_1(N)`
is in `B_A`, the class of `boone-higman-type-a-class-closed-under-finite-extensions`.

Such `N` are not non-positively curved (Svetlov; AFW arXiv:1205.0202, l.3327),
so `pi_1(N)` is not virtually special (AFW `thm:liu11`).

**Why it matters.** By `three-manifold-groups-pbh-off-nonfibered-graph-manifolds`,
this is the only case missing from `compact-3-manifold-groups-satisfy-pbh`. A
plain Boone--Higman envelope for these groups would not settle that claim,
because the plain class is not known to be closed under free products or finite
extensions.

## Attempts

1. **Linearity in characteristic zero.** *Open in the literature.* Douba,
   arXiv:2101.06797, l.206: "it is not known if a single non-NPC graph manifold
   without Sol geometry admits a faithful finite-dimensional linear
   representation over a field of characteristic zero." A faithful
   representation would settle this case through
   `char-zero-linear-groups-satisfy-permutational-boone-higman`.
2. **Positive characteristic, unitary.** *Dead.*
   - Same line: Button proved that a finitely generated group linear in positive
     characteristic acts properly by semisimple isometries on a complete CAT(0)
     space, and Leeb showed this forces a graph manifold to be NPC.
   - For one JSJ torus and product blocks, the abstract rules out faithful
     unitary representations as well.
   - A mixed-characteristic product embedding (as in
     `quasi-linear-groups-satisfy-permutational-boone-higman`) would need its
     characteristic-zero factor to be faithful on the kernel of the others. Not
     examined.
3. **Mapping class group of the fibre.** *Unavailable by hypothesis.* The
   fibered argument of `virtually-fibered-3-manifold-pbh-proof` needs a fibre.
4. **Rigid permutation groups of the JSJ tree (BLIW, arXiv:2408.05673).** *Dead as
   stated.* Their rigid permutation groups are defined for groups acting on
   locally finite graphs (TeX l.283, l.287, l.360). The JSJ Bass--Serre tree has
   edge groups `Z^2` of infinite index in the Seifert vertex groups, so it is not
   locally finite.
5. **HNN realization on an actor's set.** *Unclear.*
   `stable-permutation-hnn-of-type-a-actor-is-type-a` needs the edge group to
   have finitely many orbits on the actor's set. For an edge group `Z^2`, no type
   (A) actor containing a Seifert vertex group on such a set is known.
6. **Other mapping class group hosts.** *Untested.* Does `pi_1(N)` embed in
   `Mod(S)` for some punctured surface `S`, with the Seifert blocks
   `F_v x Z` realized by point-pushing subgroups and multitwists? That would put
   it in `B_A` through `punctured-surface-mcgs-satisfy-permutational-boone-higman`.
   The literature searched records no such embedding.
