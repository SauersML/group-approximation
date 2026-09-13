---
rg: 2
id: every-type-f-group-has-a-contractible-rips-complex
kind: claim
title: Every group of type F has a contractible Rips complex for some finite generating set and scale
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for the single group Z^n with its standard generators; this quantifies over all groups of type F and allows any generating set
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick model for proper actions of hyperbolic groups; this is a universal statement over groups of type F
  f-infinity-finite-cd-groups-have-contractible-rips: that is the affirmative answer to Problem 4.6 over groups of type F_infinity with finite cd, which implies this one; this is the affirmative answer to Problem 4.7 over groups of type F
  amenable-automatic-groups-have-contractible-rips-complexes: that is the affirmative answer to Problem 4.1 for amenable automatic groups; this is the affirmative answer to Problem 4.7 for groups of type F
  type-fn-groups-have-n-minus-1-connected-rips-complexes: that asks for (n-1)-connected Rips complexes of groups of type F_n; this asks for contractible Rips complexes of groups of type F
---

For every group `G` of type F there are a finite generating set `S` and a scale
`r ≥ 0` such that the Rips complex `VR_r(G, d_S)` is contractible.

Equivalently (`group-rips-complexes-are-cayley-graph-flag-complexes`): every group of
type F acts freely, cocompactly and transitively on the vertices of a contractible
locally finite flag simplicial complex.

This is the affirmative answer to Zaremsky's Problem 4.7 under the literal reading;
see `zaremsky-4-07-type-f-groups-have-contractible-rips`.

## Attempts

- **Established classes** (z4-07-type-f-rips, 2026-09-13; the last three unreviewed):
  torsion-free asymptotically CAT(0) groups
  (`torsion-free-asymptotically-cat0-groups-have-contractible-rips`); torsion-free coarsely
  injective groups (`coarsely-injective-groups-have-contractible-rips-complexes`); torsion-free
  finite-index subgroups of hierarchically hyperbolic groups
  (`torsion-free-hhg-subgroups-have-contractible-rips-complexes`); Helly groups
  (`helly-groups-have-contractible-rips-complexes`). Closure under direct products
  (`contractible-rips-groups-closed-under-direct-products`) and finite-edge-group splittings
  (`rips-type-r-closed-under-finite-edge-group-splittings`) enlarges these.
- **Where it stops.** Each proof uses a model space in which every finite set of diameter `t`
  lies in a ball of radius `< t` whose centre is compatible with all other such centres
  (Zaremsky's criterion, `zaremsky-rips-contractibility-criterion`), or
  Helly ball intersections. A general group of type F has no such model. Next test object:
  the integral Heisenberg group `H_3(Z)` acting on the real Heisenberg group with a
  left-invariant metric. Two things to check: whether sets of diameter `t` lie in balls of
  radius `J t + O(1)` with `J < 1`, and whether the centre-compatibility clause holds with
  distorted centres.
- **A direct construction for `H_3(Z)`, unfinished.** In coordinates `(a,b,c)`, left
  multiplication is affine on `R^3`, `y` acts as a translation in `b`, and `x, z` preserve
  each plane `b = n`. So an invariant triangulation of `R^3` with vertex set `Z^3` can be
  assembled from translates of one slab `0 ≤ b ≤ 1`. The bottom face carries the hexagonal
  lattice triangulation with edge vectors `x, z, xz`; in plane coordinates
  `(a, c − b a)` the top face carries its flip `(1,0), (0,1), (1,−1)`. The slab itself can be
  triangulated by the Cayley trick, with Delaunay heights
  `ξ_1^2 − ξ_1ξ_2 + ξ_2^2` below and `ξ_1^2 + ξ_1ξ_2 + ξ_2^2` above, perturbed. Such a
  complex is contractible (it is `R^3`) and `H_3(Z)` acts simply transitively on its vertices.
  The missing step is flagness: a crossing edge exists iff two hexagons from different
  tilings meet, and these hexagons are of comparable size. That suggests 5-cliques and
  hence a non-flag complex. The check is finite and periodic, and has not been done.
