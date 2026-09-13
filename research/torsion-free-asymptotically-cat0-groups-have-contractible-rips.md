---
rg: 2
id: torsion-free-asymptotically-cat0-groups-have-contractible-rips
kind: claim
title: Every torsion-free asymptotically CAT(0) group has a contractible Rips complex for some finite generating set
distinct_from:
  asymptotically-cat0-orbits-have-contractible-rips-complexes: that is Zaremsky's statement about the orbit with the induced metric of the ambient space; this rewrites it as a Rips complex of the group with a word metric
  every-type-f-group-has-a-contractible-rips-complex: that is the universal affirmative answer to Problem 4.7; this proves the property for torsion-free asymptotically CAT(0) groups only
  amenable-automatic-groups-have-contractible-rips-complexes: that is the open claim of Problem 4.1 for amenable automatic groups; this is an established claim for torsion-free groups acting geometrically on asymptotically CAT(0) spaces
---

Let `G` be torsion-free and act geometrically on a proper asymptotically CAT(0) geodesic
space `𝔛` (for example a torsion-free CAT(0) group or a torsion-free hyperbolic group),
and let `x_0 ∈ 𝔛`. Then for some `t` the set `T = {g ≠ 1 : d(x_0, g x_0) ≤ t}` is a
finite symmetric generating set of `G` and the Rips complex `R_1(G, T)`, the clique
complex of `Cay(G, T)`, is contractible.

So Problem 4.7 has a positive answer, in the reading "some finite generating set, some
scale" of `zaremsky-4-07-type-f-groups-have-contractible-rips`, for these groups.

Proof: route `asymptotically-cat0-groups-rips-proof`. This is a rephrasing of Zaremsky's
Proposition 6.1; its only content beyond the import is the orbit-to-Cayley-graph
identification.
