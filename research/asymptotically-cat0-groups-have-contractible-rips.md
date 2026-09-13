---
rg: 2
id: asymptotically-cat0-groups-have-contractible-rips
kind: claim
title: Every group acting geometrically on an asymptotically CAT(0) space has a contractible Rips complex, torsion allowed
distinct_from:
  torsion-free-asymptotically-cat0-groups-have-contractible-rips: that is the torsion-free case, where the orbit map is a bijection; this allows finite point stabilizers by collapsing twin vertices, which is needed for groups with torsion such as crystallographic groups
  asymptotically-cat0-orbits-have-contractible-rips-complexes: that is Zaremsky's theorem about the orbit with the metric induced from the space; this turns it into a contractible word-metric Rips complex of the group itself
---

**ESTABLISHED** (route `asymptotically-cat0-groups-have-contractible-rips-proof`).

Let `G` act geometrically (properly discontinuously and cocompactly, by isometries) on
a proper asymptotically CAT(0) geodesic metric space `𝔛`, for example a CAT(0)
space, and let `x_0 ∈ 𝔛`. Then there is `t` such that, for
`S_t = {g ∈ G ∖ {1} : d(x_0, g x_0) <= t}`, the Rips complex `P_1(G, S_t)` (the
flag complex of `Cay(G, S_t)`) is contractible.

Consequences:

- every CAT(0) group has a contractible Rips complex, even with torsion;
- every finitely generated virtually abelian group has one
  (`virtually-abelian-groups-have-contractible-rips-complexes`).
